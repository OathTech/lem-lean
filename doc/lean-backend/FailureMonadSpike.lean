import F_let_unused

/- Design evidence only: hand-prototyped emission of the comprehensive
   parity probes, not a backend implementation. The benchmark uses exactly
   f_let_unused's last step. String rendering uses the same generated function.
   Rebuild and measure with failure-monad-spike.py (beside this source). -/
namespace FailureMonadSpike

abbrev Result := Except String

def checkedPred (msg : String) (n : Nat) : Result Nat :=
  if n == 0 then .error msg else .ok (n - 1)

def unused (n : Nat) : Result String := do
  let _x ← checkedPred "let_unused: discarded e1 failed" n
  pure (String.append "after (must not print): " (Lem_String_extra.stringFromNat n))

def branch (n : Nat) : Result String := do
  let x ← checkedPred "let_float_branch: e1 failed" n
  pure (if n == 7 then String.append "used: " (Lem_String_extra.stringFromNat x)
        else String.append "after (must not print): " (Lem_String_extra.stringFromNat n))

def closure (n : Nat) : Result String := do
  let x ← checkedPred "let_float_closure: e1 failed" n
  let g := fun (_u : Unit) => String.append "used: " (Lem_String_extra.stringFromNat x)
  pure (if n == 7 then g () else String.append "after (must not print): " (Lem_String_extra.stringFromNat n))

def positive (msg : String) (n : Nat) : Result Unit :=
  if n == 0 then .error msg else .ok ()

def discarded (n : Nat) : Result String := do
  let _ ← positive "let_seq: discarded e1 failed" n
  pure (String.append "after (must not print): " (Lem_String_extra.stringFromNat n))

def unitPattern (n : Nat) : Result String := do
  let u ← positive "let_unit: discarded e1 failed" n
  match u with
  | () => pure (String.append "after (must not print): " (Lem_String_extra.stringFromNat n))

/- A3: construction may fail BEFORE the returned closure is applied.
   The non-function result at this stage prevents eta expansion across it. -/
def buildClosure (n : Nat) : Result (Unit → Result Nat) := do
  let x ← checkedPred "closure construction" n
  pure (fun _ => .ok x)

/- A4: the right argument is bound first; the body ignores both values. -/
def arguments (left right : Nat) : Result Nat := do
  let _r ← checkedPred "right" right
  let _l ← checkedPred "left" left
  pure 42

/- The strict computation is retained BEFORE substituting an inline body. -/
def inlineWitness (n : Nat) : Result Nat := do
  let _x ← if n == 0 then .error "inline check failed" else .ok n
  pure 42

/- Library callback scheduling follows library/list.lem, including its
   counter transition. The monad parameter permits both failure and trace
   witnesses without instrumenting either timed binary. -/
def mapTrM {m : Type → Type} [Monad m] {a b : Type}
    (acc : List b) (f : a → m b) (xs : List a) : m (List b) :=
  match xs with
  | [] => pure acc.reverse
  | x :: tail => do
    let y ← f x
    mapTrM (y :: acc) f tail

def countMapM {m : Type → Type} [Monad m] {a b : Type}
    (f : a → m b) (xs : List a) (counter : Nat) : m (List b) :=
  match xs with
  | [] => pure []
  | x :: tail => do
    let ys ← if counter < 5000 then countMapM f tail (counter + 1)
              else mapTrM [] f tail
    let y ← f x
    pure (y :: ys)

def mapOracleM {m : Type → Type} [Monad m] {a b : Type}
    (f : a → m b) (xs : List a) : m (List b) := countMapM f xs 0

def orderWitness (n : Nat) : List Nat :=
  let callback : Nat → StateM (List Nat) Nat := fun x => do
    modify (x :: ·)
    pure x
  ((mapOracleM callback ((List.range n).map (· + 1))).run []).2.reverse

def firstFailure (n left right : Nat) : Result (List Nat) :=
  mapOracleM (fun x => if x == left || x == right then .error (toString x) else .ok x)
    ((List.range n).map (· + 1))

/- Keep the source list-of-functions interface in both timed variants.
   Selecting the callback in every iteration is intentional and symmetric. -/
def steps : List (Nat → Result String) :=
  [fun n => .ok (String.append "before: " (Lem_String_extra.stringFromNat n)),
   fun n => .ok (String.append "tuple used: " (Lem_String_extra.stringFromNat ((n + 1) + (n + 2)))),
   unused]

theorem error_absorbs (msg : String) (k : Nat → Result String) :
    (Except.error msg >>= k) = Except.error msg := rfl

theorem inline_failure : inlineWitness 0 = .error "inline check failed" := rfl

theorem map_short_order : orderWitness 3 = [3, 2, 1] := rfl

theorem map_short_failure : firstFailure 3 1 3 = .error "3" := rfl

theorem probe_failures :
    unused 0 = .error "let_unused: discarded e1 failed" ∧
    branch 0 = .error "let_float_branch: e1 failed" ∧
    closure 0 = .error "let_float_closure: e1 failed" ∧
    discarded 0 = .error "let_seq: discarded e1 failed" ∧
    unitPattern 0 = .error "let_unit: discarded e1 failed" ∧
    buildClosure 0 = .error "closure construction" ∧
    arguments 0 0 = .error "right" := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem unused_success (n : Nat) (s : String) (h : unused n = .ok s) :
    (_root_.steps[2]!) n = s := by
  simp only [unused, checkedPred] at h
  split at h
  · cases h
  · change Except.ok (String.append "after (must not print): " (Lem_String_extra.stringFromNat n)) = Except.ok s at h
    simpa [_root_.steps, lemSeq] using Except.ok.inj h

#print axioms error_absorbs
#print axioms inline_failure
#print axioms map_short_order
#print axioms map_short_failure
#print axioms probe_failures
#print axioms unused_success

end FailureMonadSpike
