/- Arc-8 audit fix (auditor A F1): panic-path pin for the L_undefined
   rendering. `head_undef []` reaches the pattern-compiler's
   incomplete-match arm, which the backend now emits as an ascribed
   failwithI carrying the Incomplete Pattern message (mirroring the
   OCaml backend's `failwith m`, src/backend.ml:864) — never a silent
   `default`.

   Run by the Makefile `lean-panic` target in TWO legs (the accurate
   panic semantics — auditor A N2): failwithI = Lean `panic!`.
   - No env var (library-call semantics): the panic PRINTS the
     Incomplete Pattern message and CONTINUES with the Inhabited
     default — the run must show the PANIC line with the message AND
     the post-panic `survived:` line. Pre-fix, head_undef [] printed
     NOTHING (silent default); the message line is the pin of the fix.
   - LEAN_ABORT_ON_PANIC=1 (the harness discipline, cerberus
     scripts/common.sh): the process must fail-stop (nonzero exit).
     Toolchain caveat (4.28): closed-term extraction is EAGER here, so
     LemLib's own ground failwithI arms (e.g. List_extra.tail's []
     arm) panic-silently inside module INIT — the abort fires there,
     before main, and the message cannot be observed on this leg. On
     ≥4.32 closed terms are lazy (lean_obj_once) and the
     abort-with-message path is covered by the cerberus differential
     suites.

   The argument list is derived from argv: a closed `head_undef []`
   call would itself be lifted into a module initializer, where the
   runtime evaluates closed terms with panic messages DISABLED
   (lean_set_panic_messages(false) in the emitted init code) — the
   no-env leg would then see neither message nor survival marker. -/
import Test_failwith_threading

def main (args : List String) : IO Unit := do
  -- Runtime data (argv) — not closed-term-extractable. Run with no
  -- arguments: the list is [] and head_undef takes the incomplete-match
  -- arm.
  let l : List Nat := args.map String.length
  let n : Nat := head_undef l
  -- Library-call semantics: reached AFTER the panic printed (no-env
  -- leg); must never be reached under LEAN_ABORT_ON_PANIC=1.
  IO.println s!"survived: {n}"
