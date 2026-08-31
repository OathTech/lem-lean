/- Hand-written support for test_tuple_let_once.lem (the m7
   single-evaluation pin): a process-global counter behind a
   hand-written impure-extern pattern (unsafe impl + implemented_by
   opaque). Since the effect-retirement arc deleted the backend's
   effectful mechanism (runEffectful + generated attribute armour),
   the pure-typed boundary AND its armour live entirely in this test
   scaffold: `tickPair` carries `never_extract` so the compiler can
   neither cache a closed `tickPair ()` application as a startup
   constant nor CSE two call sites — the number of RHS evaluations
   stays observable in the values the destructuring let binds: one
   evaluation gives (1, 2); a duplicated RHS gives the second binding
   (3, 4). This models exactly the class of hand-written impure
   externs that the retirement leaves to consumers' own armour. -/

namespace TupleLetTick

@[never_extract, noinline]
private unsafe def counterImpl : IO.Ref Nat :=
  unsafeBaseIO (IO.mkRef 0)

@[implemented_by counterImpl]
private opaque counter : IO.Ref Nat

private def tickIO : BaseIO Nat :=
  counter.modifyGet (fun n => (n + 1, n + 1))

private def tickPairIO : BaseIO (Nat × Nat) := do
  let a ← tickIO
  let b ← tickIO
  pure (a, b)

@[never_extract, noinline]
private unsafe def tickPairImpl (_ : Unit) : Nat × Nat :=
  unsafeBaseIO tickPairIO

@[implemented_by tickPairImpl]
opaque tickPair : Unit → Nat × Nat

attribute [never_extract] tickPair

end TupleLetTick
