/- Compiled-binary leg of the integer division/remainder parity pin
   (see test_integer_div.lem): re-asserts the Euclidean values at
   RUNTIME. The suite's elaborator asserts evaluate in the
   interpreter; compiled Int arithmetic is GMP-backed, so runtime
   agreement is asserted here, not assumed. Expected values are the
   measured Nat_big_num.div/modulus outputs of the OCaml oracle. -/

import Test_integer_div

def main : IO UInt32 := do
  let divs := [div_m7_2, div_7_m2, div_m7_m2, div_7_2, div_m1_3, div_1_m3]
  let mods := [mod_m7_2, mod_7_m2, mod_m7_m2, mod_7_2, mod_m1_3, mod_1_m3]
  IO.println s!"div: {divs}"
  IO.println s!"mod: {mods}"
  if divs == [-4, -3, 4, 3, -1, 0] && mods == [1, 1, 1, 1, 2, 1]
     && op_div == -4 && op_mod == 1 then
    IO.println "integer division parity: OK"
    return 0
  else
    IO.println "integer division parity FAILED: values diverge from the OCaml oracle (Nat_big_num Euclidean semantics)"
    return 1
