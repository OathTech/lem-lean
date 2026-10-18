#!/usr/bin/env python3
"""Rebuildable, bounded design experiment; all output lives under .tmp.

After the repository's root make and comprehensive baseline:
  python3 doc/lean-backend/failure-monad-spike.py build
  CERB_MEM_MAX=16G scripts/capped python3 doc/lean-backend/failure-monad-spike.py measure --count 30000000 --repeats 6

Builds are sequential through the repository's scripts/capped. Measurement
invokes ONLY the already compiled binaries, alternates their order, and checks
every exit, checksum and failure message. It uses GNU time plus perf_counter;
startup/terminal-failure controls use count=0. No raw measurement output is committed.
The workload has count successful checked calls and one terminal call, so it
measures propagation checks on the success path and terminal failure, not an
error-heavy service that recovers from many failures.
"""
import argparse
import csv
import os
from pathlib import Path
import re
import resource
import shutil
import statistics
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
OUT = ROOT / ".tmp/failure-monad/spike"
PROBES = ["f_let_float_branch", "f_let_float_closure", "f_let_seq",
          "f_let_unit", "f_let_unused"]
FUNS = ["branch", "closure", "discarded", "unitPattern", "unused"]


def run(cmd, cwd=ROOT):
    print("+", " ".join(map(str, cmd)), flush=True)
    subprocess.run(list(map(str, cmd)), cwd=cwd, check=True, timeout=600)


def driver(prototype):
    get = ("match FailureMonadSpike.unused n with\n"
           "    | .error msg => throw (IO.userError msg)\n"
           "    | .ok s => pure s" if prototype else "pure ((steps[2]!) n)")
    terminal = ("match FailureMonadSpike.unused terminal with\n"
                "  | .error msg => IO.eprintln msg; return 2\n"
                "  | .ok s => IO.println s; return 0" if prototype else
                "IO.println ((steps[2]!) terminal)\n  return 0")
    return f"""import {'FailureMonadSpike' if prototype else 'F_let_unused'}
def main (args : List String) : IO UInt32 := do
  let [countS, seedS, terminalS] := args | throw (IO.userError "expected count seed terminal")
  let some count := countS.toNat? | throw (IO.userError "invalid count")
  let some seed := seedS.toNat? | throw (IO.userError "invalid seed")
  let some terminal := terminalS.toNat? | throw (IO.userError "invalid terminal")
  let mut checksum : Nat := 0
  for i in [:count] do
    let n := (seed + i) % 1024 + 1
    let s ← {get}
    checksum := checksum + s.length
  IO.println s!"checksum: {{checksum}}"
  (← IO.getStdout).flush
  {terminal}
"""


def build():
    os.environ.setdefault("CERB_MEM_MAX", "16G")
    OUT.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(ROOT / "lean-lib/lean-toolchain", OUT / "lean-toolchain")
    shutil.copyfile(HERE / "FailureMonadSpike.lean", OUT / "FailureMonadSpike.lean")
    for probe in PROBES:
        run([ROOT / "lem", "-wl", "ign", "-i", ROOT / "library/pervasives_extra.lem",
             "-lean", "-outdir", OUT, ROOT / f"tests/comprehensive/parity/probes/{probe}.lem"])
    (OUT / "CurrentMain.lean").write_text(driver(False))
    (OUT / "PrototypeMain.lean").write_text(driver(True))
    lake = ('import Lake\nopen Lake DSL\npackage FailureMonadDesign\n'
            'require LemLib from "../../../lean-lib"\n'
            'lean_lib Spike where\n  roots := #[`FailureMonadSpike, '
            '`F_let_unused, `F_let_float_branch, `F_let_float_closure, '
            '`F_let_seq, `F_let_unit]\n'
            'lean_exe current where\n  root := `CurrentMain\n'
            'lean_exe prototype where\n  root := `PrototypeMain\n')
    for probe, fun in zip(PROBES, FUNS):
        module = probe[0].upper() + probe[1:]
        name = "Probe_" + probe
        (OUT / (name + ".lean")).write_text(f"""import FailureMonadSpike
def main (args : List String) : IO UInt32 := do
  let n := args.length
  IO.println ("before: " ++ Lem_String_extra.stringFromNat n)
  {'IO.println ("tuple used: " ++ Lem_String_extra.stringFromNat ((n + 1) + (n + 2)))' if fun == 'unused' else ''}
  (← IO.getStdout).flush
  match FailureMonadSpike.{fun} n with
  | .error msg => IO.eprintln msg; return 2
  | .ok s => IO.println s; return 0
""")
        lake += f'lean_exe "{probe}" where\n  root := `{name}\n'
        # Build the actual old emission too, independently of suite outputs.
        name_old = "Old_" + probe
        (OUT / (name_old + ".lean")).write_text(f"""import {module}
def main (args : List String) : IO Unit := steps.forM fun f => do
  IO.println (f args.length)
  (← IO.getStdout).flush
""")
        lake += f'lean_exe "old-{probe}" where\n  root := `{name_old}\n'
    (OUT / "lakefile.lean").write_text(lake)
    cap = ROOT / "scripts/capped"
    run([cap, "lake", "build", "Spike", "current", "prototype", *PROBES,
         *("old-" + p for p in PROBES)], OUT)
    run([cap, "lake", "env", "leanchecker", "--fresh", "FailureMonadSpike"], OUT)
    for probe in PROBES:
        old = execute("old-" + probe, [])
        new = execute(probe, [])
        pin = (ROOT / f"tests/comprehensive/parity/expected/{probe}.out").read_text()
        assert new.returncode == 2 and new.stdout == pin, (probe, new)
        assert "failed" in new.stderr, (probe, new.stderr)
        if "float" in probe:
            assert old.returncode == 0 and "after (must not print)" in old.stdout, old
        else:
            assert old.returncode == -6 and old.stdout == pin, old
        for n in (1, 7):
            old = execute("old-" + probe, ["x"] * n)
            new = execute(probe, ["x"] * n)
            assert old.returncode == new.returncode == 0, (old, new)
            assert old.stdout == new.stdout and not old.stderr and not new.stderr, (old, new)
        print(f"{probe}: prototype failure prefix matches oracle pin; success controls 1,7 match current")


def no_core():
    resource.setrlimit(resource.RLIMIT_CORE, (0, 0))


def execute(name, args, timed=False):
    binary = OUT / ".lake/build/bin" / name
    cmd = [str(binary), *map(str, args)]
    if timed:
        cmd = ["/usr/bin/time", "-f", "METRIC %e %U %S %M", *cmd]
    return subprocess.run(cmd, env={**os.environ, "LEAN_ABORT_ON_PANIC": "1",
                                   "LEAN_BACKTRACE": "0"},
                          capture_output=True, text=True, timeout=60, preexec_fn=no_core)


def measure(count, repeats):
    if count <= 0 or repeats < 3:
        raise ValueError("count must be positive and repeats at least three")
    rows = []
    for mode, size, terminal in [("startup", 0, 1), ("startup-failure", 0, 0),
                                  ("success", count, 1), ("failure", count, 0)]:
        expected = sum(len("after (must not print): " + str((12345 + i) % 1024 + 1))
                       for i in range(size))
        for rep in range(repeats):
            order = ("current", "prototype") if rep % 2 == 0 else ("prototype", "current")
            for variant in order:
                t = time.perf_counter()
                p = execute(variant, [size, 12345, terminal], timed=True)
                wall = time.perf_counter() - t
                expected_rc = 0 if terminal else (134 if variant == "current" else 2)
                assert p.returncode == expected_rc, (mode, variant, p)
                expected_out = f"checksum: {expected}\n"
                if terminal:
                    expected_out += "after (must not print): 1\n"
                assert p.stdout == expected_out, (mode, variant, p.stdout, expected_out)
                if not terminal:
                    assert "let_unused: discarded e1 failed" in p.stderr, p.stderr
                match = re.search(r"^METRIC (\S+) (\S+) (\S+) (\S+)$", p.stderr, re.M)
                if match is None:
                    raise RuntimeError(p.stderr)
                elapsed, user, system, rss = match.groups()
                row = dict(mode=mode, repeat=rep + 1, variant=variant, count=size,
                           wall_s=f"{wall:.6f}", time_s=elapsed, user_s=user,
                           sys_s=system, rss_kb=rss, exit=p.returncode)
                rows.append(row)
                print(row, flush=True)
    with (OUT / "timings.csv").open("w") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0]))
        w.writeheader()
        w.writerows(rows)
    for mode in ("startup", "startup-failure", "success", "failure"):
        for variant in ("current", "prototype"):
            rs = [r for r in rows if r["mode"] == mode and r["variant"] == variant]
            ws = [float(r["wall_s"]) for r in rs]
            cpu = [float(r["user_s"]) + float(r["sys_s"]) for r in rs]
            print(f"{mode} {variant}: wall median={statistics.median(ws):.6f} "
                  f"range={min(ws):.6f}..{max(ws):.6f}; "
                  f"cpu median={statistics.median(cpu):.3f}; "
                  f"max_rss_kb={max(int(r['rss_kb']) for r in rs)}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=["build", "measure"])
    parser.add_argument("--count", type=int, default=30000000)
    parser.add_argument("--repeats", type=int, default=6)
    args = parser.parse_args()
    if args.action == "build":
        build()
    else:
        measure(args.count, args.repeats)
