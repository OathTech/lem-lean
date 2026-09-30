#!/usr/bin/env python3
"""Library parity coverage (2026-09-30, [AGENT]): which named `val`
declarations of library/*.lem have BOTH an OCaml and a Lean realisation,
and which of those are referenced by a parity probe.

Realisation (per target t in {ocaml, lean}):
  - `declare <T> target_rep function NAME` with t in T, or
  - a `let [inline] [rec] [T|~T] NAME` / `and NAME` definition whose target
    set admits t (no set = every target), or
  - NAME is a class method (realised by the instances).
A val whose type mentions rational/real/float64/float32, or whose Lean
target_rep is a `LemUnsupported.` refusal, has no Lean realisation.
A val with neither realisation for a target is "not for" that target.

Reference (a heuristic, the same metric before/after): NAME occurs as a
word in a probe (comments stripped). If NAME is declared in more than one
library module, only a qualified `Module.NAME` counts: which module an
unqualified use resolves to is not guessed (conservative).
Operators (`val (+)` etc.) are not counted. Class-dispatched uses
(`+` at nat reaching natAdd) are NOT counted: the probes call the named
functions directly for this reason.

Usage: lib_coverage.py [--list-uncovered] [--module M]  (fails if the
library or probe directory is empty — no vacuous 0/0).
"""
import os, re, sys, glob, collections

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "../../../.."))
LIB = os.path.join(ROOT, "library")
PROBES = os.path.join(HERE, "..", "probes")
TARGETS = ("ocaml", "lean")

def strip_comments(s):
    out, depth, i = [], 0, 0
    while i < len(s):
        if s.startswith("(*", i): depth += 1; i += 2; continue
        if depth and s.startswith("*)", i): depth -= 1; i += 2; continue
        if not depth: out.append(s[i])
        elif s[i] == "\n": out.append("\n")
        i += 1
    return "".join(out)

def tset(spec):
    """spec: None (all), '{a;b}' or '~{a;b}' or a single target word."""
    if spec is None: return set(TARGETS)
    spec = spec.strip()
    neg = spec.startswith("~")
    names = set(x.strip() for x in spec.strip("~{} ").split(";") if x.strip())
    return (set(TARGETS) - names) if neg else (names & set(TARGETS))

ID = r"[A-Za-z_][A-Za-z0-9_']*"
TS = r"(~?\{[^}]*\})"

def scan_module(path):
    src = strip_comments(open(path).read())
    mod = os.path.basename(path)[:-4].capitalize()
    vals, methods = [], set()
    real = collections.defaultdict(set)
    in_class = False
    unsupported = set()  # Lean realisation is a LemUnsupported refusal (class (c))
    for line in src.split("\n"):
        l = line.strip()
        if re.match(r"class\b", l): in_class = True
        if in_class and re.match(r"end\b", l): in_class = False
        m = re.match(r"val\s+(" + ID + r")\s*(\[[^\]]*\])?\s*:(.*)", l)
        if m:
            vals.append(m.group(1))
            if re.search(r"\b(rational|real|float64|float32)\b", m.group(3)): unsupported.add(m.group(1))
            if in_class: methods.add(m.group(1))
        m = re.match(r"declare\s+(" + TS + r"|[a-z]+)\s+target_rep\s+function\s+(" + ID + r")", l)
        if m:
            real[m.group(3)] |= tset(m.group(1))
            if "lean" in tset(m.group(1)) and "LemUnsupported." in l: unsupported.add(m.group(3))
        m = re.match(r"(?:let|and)\s+(?:inline\s+)?(?:rec\s+)?(?:" + TS + r"\s+)?(?:rec\s+)?(" + ID + r")", l)
        if m and m.group(2) not in ("inline", "rec"):
            real[m.group(2)] |= tset(m.group(1))
    for n in methods: real[n] |= set(TARGETS)
    for n in unsupported: real[n].discard("lean")
    return mod, vals, real, methods

def main():
    args = sys.argv[1:]
    mods = [scan_module(p) for p in sorted(glob.glob(os.path.join(LIB, "*.lem")))]
    probes = sorted(glob.glob(os.path.join(PROBES, "*.lem")))
    if not mods or not probes: sys.exit("FAIL (vacuous): no library modules or no probes")
    text = "\n".join(strip_comments(open(p).read()) for p in probes)
    owners = collections.Counter(n for _, vals, _, _ in mods for n in set(vals))
    tot_e = tot_c = 0
    rows = []
    for mod, vals, real, methods in mods:
        elig, cov, unc, skipped = [], [], [], []
        for n in dict.fromkeys(vals):
            if not set(TARGETS) <= real.get(n, set()):
                skipped.append((n, sorted(set(TARGETS) - real.get(n, set())))); continue
            elig.append(n)
            q = re.search(r"\b" + mod + r"\." + re.escape(n) + r"\b", text)
            u = owners[n] == 1 and re.search(r"(?<![A-Za-z0-9_'.])" + re.escape(n) + r"(?![A-Za-z0-9_'])", text)
            (cov if (q or u) else unc).append(n)
        tot_e += len(elig); tot_c += len(cov)
        rows.append((mod, len(vals), len(elig), len(cov), unc, skipped))
    only = args[args.index("--module") + 1] if "--module" in args else None
    print("%-16s %5s %9s %8s" % ("module", "vals", "eligible", "covered"))
    for mod, nv, ne, nc, unc, skipped in rows:
        if only and mod != only: continue
        print("%-16s %5d %9d %8d" % (mod, nv, ne, nc))
        if "--list-uncovered" in args:
            if unc: print("    uncovered: " + " ".join(unc))
            if skipped: print("    not both targets: " + " ".join("%s(no %s)" % (n, "/".join(t)) for n, t in skipped))
    print("%-16s %5s %9d %8d" % ("TOTAL", "", tot_e, tot_c))

main()
