import Init

namespace RelationCounterexample

inductive Ty where
  | nat
  | arr (a b : Ty)

def Source : Ty → Type
  | .nat => Nat
  | .arr a b => Source a → Source b

def Exec : Ty → Type
  | .nat => Nat
  | .arr a b => Exec a → Except String (Exec b)

def Rel : (t : Ty) → Nat → Source t → Exec t → Prop
  | _, 0, _, _ => True
  | .nat, _ + 1, x, y => x = y
  | .arr a b, k + 1, f, g =>
      ∀ x x', Rel a k x x' → ∀ y', g x' = .ok y' → Rel b k (f x) y'

theorem applyZero_not_related :
    ¬ Rel (.arr (.arr .nat .nat) .nat) 2
        (fun f => f (0 : Nat)) (fun f => f (0 : Nat)) := by
  intro h
  have hCallbacks : Rel (.arr .nat .nat) 1
      (fun _ => (0 : Nat)) (fun _ => .ok (1 : Nat)) := by
    intro x x' _hx y' _hy
    trivial
  have hBad : (0 : Nat) = 1 := h (fun _ => (0 : Nat)) (fun _ => .ok (1 : Nat)) hCallbacks (1 : Nat) rfl
  exact Nat.noConfusion hBad

#print axioms applyZero_not_related

/- The alternative reading keeps equality for base types even at index zero,
   and makes only arrows unconstrained there. It fails one index earlier. -/
def RelBaseEq : (t : Ty) → Nat → Source t → Exec t → Prop
  | .nat, _, x, y => x = y
  | .arr _ _, 0, _, _ => True
  | .arr a b, k + 1, f, g =>
      ∀ x x', RelBaseEq a k x x' → ∀ y', g x' = .ok y' → RelBaseEq b k (f x) y'

theorem applyZero_not_related_base_eq :
    ¬ RelBaseEq (.arr (.arr .nat .nat) .nat) 1
        (fun f => f (0 : Nat)) (fun f => f (0 : Nat)) := by
  intro h
  have hBad : (0 : Nat) = 1 :=
    h (fun _ => (0 : Nat)) (fun _ => .ok (1 : Nat)) True.intro (1 : Nat) rfl
  exact Nat.noConfusion hBad

#print axioms applyZero_not_related_base_eq

end RelationCounterexample
