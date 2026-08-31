/- Hand-written support for test_tuple_let_once.lem (the m7
   single-evaluation pin): a process-global counter behind the standard
   effectful-extern pattern (unsafe impl + implemented_by opaque, as in
   LemLib's runEffectful scaffold). tickPairIO returns two consecutive
   draws, so the number of RHS evaluations is observable in the values
   the destructuring let binds: one evaluation gives (1, 2); a
   duplicated RHS gives the second binding (3, 4). -/

namespace TupleLetTick

@[never_extract, noinline]
private unsafe def counterImpl : IO.Ref Nat :=
  unsafeBaseIO (IO.mkRef 0)

@[implemented_by counterImpl]
private opaque counter : IO.Ref Nat

def tickIO : BaseIO Nat :=
  counter.modifyGet (fun n => (n + 1, n + 1))

def tickPairIO : BaseIO (Nat × Nat) := do
  let a ← tickIO
  let b ← tickIO
  pure (a, b)

end TupleLetTick
