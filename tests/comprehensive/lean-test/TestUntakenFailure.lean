/- Driver for test_untaken_failure.lem (linksem 2026-09-28, B8/B9); run by the
   Makefile `lean-untaken-failure` target under LEAN_ABORT_ON_PANIC=1.
   No arguments: every failure branch is untaken, so the run must print
   `untaken: 0 z` and exit 0 (pre-fix: silent SIGABRT during module init).
   Argument `take`: `pick true` reaches `must_be_small 10`, which must abort
   loudly with its message. -/
import Test_untaken_failure

def main (args : List String) : IO Unit := do
  -- leg 3 (audit item 2): `failstop` runs with LemLib's fail-stop switched
  -- on and NO LEAN_ABORT_ON_PANIC: the reached failure must still stop it.
  if args == ["failstop"] then lemFailStop
  let take := args == ["take"] || args == ["failstop"]
  IO.println s!"untaken: {pick take} {pick_char 0}"
