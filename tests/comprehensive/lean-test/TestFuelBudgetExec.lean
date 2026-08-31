/- Compiled-binary behavioral test for per-declaration fuel budgets
   (charter §8.3; suite phase lean-fuel-budget). Witnesses, in a real
   binary:
   - the budgeted declaration exhausts at exactly its budget (5);
   - the UNANNOTATED sibling keeps lemDefaultFuel semantics at the
     exact 10^6 boundary — depth 999,999 completes (a budget of 5 or
     any silently-changed default would have cut it), depth 1,000,000
     exhausts (the default is exactly lemDefaultFuel, not more);
   - budget × reader composition: the wrapper keeps the
     reader-prefixed type with the budgeted literal (climbs of length
     ≤ 6 complete under budget 7; longer climbs exhaust). -/

import Test_fuel_budget

def check (name : String) (ok : Bool) : IO Bool := do
  if ok then
    IO.println s!"  ok: {name}"
  else
    IO.println s!"  FAIL: {name}"
  pure ok

def main : IO UInt32 := do
  let r1 ← check "bspin 4 = 0 [within budget 5]" (bspin 4 == 0)
  let r2 ← check "bspin 5 = 999 [exhausts at budget 5]" (bspin 5 == 999)
  let r3 ← check "dspin 999999 = 0 [unannotated runs to lemDefaultFuel]"
    (dspin 999999 == 0)
  let r4 ← check "dspin 1000000 = 999 [unannotated cuts exactly at lemDefaultFuel]"
    (dspin 1000000 == 999)
  let r5 ← check "climb 10 4 = 10 [reader x budget: completes under 7]"
    (climb 10 4 == 10)
  let r6 ← check "climb 20 4 = 998 [reader x budget: exhausts at 7]"
    (climb 20 4 == 998)
  if r1 && r2 && r3 && r4 && r5 && r6 then
    IO.println "fuel budget: OK"
    return 0
  else
    IO.println "fuel budget: FAILED"
    return 1
