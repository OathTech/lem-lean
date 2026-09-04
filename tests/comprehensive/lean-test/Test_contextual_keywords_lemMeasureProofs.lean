/- Proof of the fuel_measure obligation of test_contextual_keywords.lem
   (fuel-measure slice, 2026-09-04): the measured `count_list_measured`. -/
import Test_contextual_keywords

namespace Test_contextual_keywords_lemMeasureProofs

theorem count_list_measured_stable (l : List Nat) (f g : Nat)
    (hf : List.length l + 1 ≤ f) (hg : List.length l + 1 ≤ g) :
    count_list_measured_lemFuel f l = count_list_measured_lemFuel g l := by
  induction l generalizing f g with
  | nil =>
    cases f with
    | zero => omega
    | succ f => cases g with
      | zero => omega
      | succ g => simp [count_list_measured_lemFuel]
  | cons x xs ih =>
    cases f with
    | zero => omega
    | succ f => cases g with
      | zero => omega
      | succ g =>
        simp only [List.length_cons] at hf hg
        simp only [count_list_measured_lemFuel]
        rw [ih f g (by omega) (by omega)]

theorem count_list_measured_measure_sufficient (l : List Nat) (lemFuel : Nat)
    (lemMeasureLe : List.length l + 1 ≤ lemFuel) :
    count_list_measured_lemFuel lemFuel l = count_list_measured l :=
  count_list_measured_stable l lemFuel (List.length l + 1) lemMeasureLe (Nat.le_refl _)

end Test_contextual_keywords_lemMeasureProofs
