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

theorem error_absorbs (msg : String) (k : Nat → Result String) :
    (Except.error msg >>= k) = Except.error msg := rfl

theorem probe_failures :
    unused 0 = .error "let_unused: discarded e1 failed" ∧
    branch 0 = .error "let_float_branch: e1 failed" ∧
    closure 0 = .error "let_float_closure: e1 failed" ∧
    discarded 0 = .error "let_seq: discarded e1 failed" ∧
    unitPattern 0 = .error "let_unit: discarded e1 failed" ∧
    buildClosure 0 = .error "closure construction" ∧
    arguments 0 0 = .error "right" := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem unused_success (n : Nat) (s : String) (h : unused n = .ok s) :
    (steps[2]!) n = s := by
  simp only [unused, checkedPred] at h
  split at h
  · cases h
  · change Except.ok (String.append "after (must not print): " (Lem_String_extra.stringFromNat n)) = Except.ok s at h
    simpa [steps, lemSeq] using Except.ok.inj h

#print axioms error_absorbs
#print axioms probe_failures
#print axioms unused_success

end FailureMonadSpike
