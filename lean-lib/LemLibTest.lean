import LemLib

/-!
# LemLibTest — Fmap representation-change equivalence (arc-6 S3)

The Fmap representation changed from an assoc list (newest-first cons spine,
`fmapAdd` = cons + BEq-filter, `fmapLookupBy` = linear comparator scan) to a
comparator-keyed `Std.TreeMap` index + insertion-order spine index (see the
Fmap section of LemLib.lean). This file carries the equivalence obligations
(D7 doctrine: in-Lean agreement is a theorem where feasible):

1. `LemLibLegacy` — the retired reference implementation, verbatim,
   test-only.
2. Kernel-checked THEOREMS: under the stated comparator laws
   (`Std.TransCmp` of the lifted comparator) and BEq/comparator coherence
   (`a == b → cmp a b = EQ` — the "assumption 2" of the design note), the
   new and the retired implementations assign EQUAL `lookup` results to
   EVERY sequence of insert/delete operations (`lookup_equiv`), via
   per-operation characteristic laws proved for BOTH implementations.
3. Bounded-exhaustive PROPERTY TESTS for the observables whose bit-for-bit
   list-level equivalence is not kernel-proved (enumeration ORDER of
   `fmapElements`/folds, domain/range/all/map/mapi/union/equalBy/isEmpty):
   every operation sequence up to the stated depth over small key spaces is
   checked new-vs-old, including an adversarial key type whose BEq is
   strictly finer than its comparator (the cerberus `sym`/`identifier`
   situation, which exercises the bucket machinery).

Proved/unproved split (recorded for the S3 report): the general
order-observable equivalence through the two-tree bookkeeping requires a
full byKey/bySeq coherence invariant over `Std.TreeMap` internals and is
documented-deliberate unproved (disproportionate for this slice); the
lookup observable is proved for all reachable maps.
-/

set_option autoImplicit false

/- ========================================================================
   The retired reference implementation (pre-arc-6-S3 LemLib.lean, verbatim
   modulo the namespace). Test-only: nothing outside this file may use it.
   ======================================================================== -/
namespace LemLibLegacy

variable {α β γ : Type}

abbrev Fmap (α β : Type) := List (α × β)

def fmapEmpty : Fmap α β := []
@[inline] def fmapIsEmpty : Fmap α β → Bool := List.isEmpty

def fmapAdd [BEq α] (k : α) (v : β) (m : Fmap α β) : Fmap α β :=
  (k, v) :: m.filter (fun p => !(p.1 == k))

def fmapLookupBy (cmp : α → α → LemOrdering) (k : α) : Fmap α β → Option β
  | [] => none
  | (k', v) :: rest => match cmp k k' with
    | .EQ => some v
    | _ => fmapLookupBy cmp k rest

def fmapDeleteBy (cmp : α → α → LemOrdering) (k : α) (m : Fmap α β) : Fmap α β :=
  m.filter (fun p => match cmp k p.1 with | .EQ => false | _ => true)

def fmapMap (f : β → γ) (m : Fmap α β) : Fmap α γ :=
  m.map (fun p => (p.1, f p.2))

def fmapMapi (f : α → β → γ) (m : Fmap α β) : Fmap α γ :=
  m.map (fun p => (p.1, f p.1 p.2))

def fmapEqualBy (eqK : α → α → Bool) (eqV : β → β → Bool) (m1 m2 : Fmap α β) : Bool :=
  let check (m1 m2 : Fmap α β) : Bool :=
    m1.all (fun (k, v) =>
      match m2.find? (fun (k', _) => eqK k k') with
      | some (_, v') => eqV v v'
      | none => false)
  check m1 m2 && check m2 m1

def fmapDomainBy (cmp : α → α → LemOrdering) (m : Fmap α β) : List α :=
  setFromListBy cmp (m.map (fun p => p.1))

def fmapRangeBy (cmp : β → β → LemOrdering) (m : Fmap α β) : List β :=
  setFromListBy cmp (m.map (fun p => p.2))

def fmapAll (f : α → β → Bool) (m : Fmap α β) : Bool :=
  m.all (fun p => f p.1 p.2)

def fmapUnion [BEq α] (m1 m2 : Fmap α β) : Fmap α β :=
  m2.foldl (fun acc (k, v) => fmapAdd k v acc) m1

@[inline] def fmapElements (m : Fmap α β) : List (α × β) := m

end LemLibLegacy

namespace LemLibTest

/- ========================================================================
   Reified operation sequences: the reachable-map quantifier.
   ======================================================================== -/

inductive Op (α β : Type) where
  | add (k : α) (v : β)
  | del (k : α)

variable {α β : Type}

def applyNew [BEq α] (c : α → α → LemOrdering) (m : Fmap α β) : List (Op α β) → Fmap α β
  | [] => m
  | .add k v :: ops => applyNew c (fmapAddBy c k v m) ops
  | .del k :: ops => applyNew c (fmapDeleteBy c k m) ops

def applyOld [BEq α] (c : α → α → LemOrdering) (l : LemLibLegacy.Fmap α β) :
    List (Op α β) → LemLibLegacy.Fmap α β
  | [] => l
  | .add k v :: ops => applyOld c (LemLibLegacy.fmapAdd k v l) ops
  | .del k :: ops => applyOld c (LemLibLegacy.fmapDeleteBy c k l) ops

/- ========================================================================
   Kernel-checked equivalence: the lookup observable.
   ======================================================================== -/

section Theorems

variable (c : α → α → LemOrdering)

/-- `lemCmpToOrd` hits `.eq` exactly on `.EQ`. -/
theorem lemCmpToOrd_eq_iff {a b : α} : lemCmpToOrd c a b = .eq ↔ c a b = .EQ := by
  unfold lemCmpToOrd
  cases c a b <;> simp

/-- EQ-symmetry of the comparator, from the `OrientedCmp` part of `TransCmp`. -/
theorem cEq_symm [Std.OrientedCmp (lemCmpToOrd c)] {a b : α}
    (h : c a b = .EQ) : c b a = .EQ := by
  exact (lemCmpToOrd_eq_iff c).mp
    (Std.OrientedCmp.eq_symm (cmp := lemCmpToOrd c) ((lemCmpToOrd_eq_iff c).mpr h))

/-- EQ-transitivity of the comparator, from `TransCmp`. -/
theorem cEq_trans [Std.TransCmp (lemCmpToOrd c)] {a b d : α}
    (h1 : c a b = .EQ) (h2 : c b d = .EQ) : c a d = .EQ := by
  exact (lemCmpToOrd_eq_iff c).mp
    (Std.TransCmp.eq_trans (cmp := lemCmpToOrd c)
      ((lemCmpToOrd_eq_iff c).mpr h1) ((lemCmpToOrd_eq_iff c).mpr h2))

/-- On non-EQ, `lemCmpToOrd` is not `.eq`. -/
theorem lemCmpToOrd_ne_eq {a b : α} (h : c a b ≠ .EQ) : lemCmpToOrd c a b ≠ .eq :=
  fun hc => h ((lemCmpToOrd_eq_iff c).mp hc)

/-- Base facts: the empty map. -/
theorem lookup_empty (k : α) : fmapLookupBy c k (fmapEmpty : Fmap α β) = none := rfl
theorem elements_empty : fmapElements (fmapEmpty : Fmap α β) = [] := rfl
theorem isEmpty_empty : fmapIsEmpty (fmapEmpty : Fmap α β) = true := rfl
theorem legacy_lookup_empty (k : α) :
    LemLibLegacy.fmapLookupBy c k (LemLibLegacy.fmapEmpty : LemLibLegacy.Fmap α β) = none := rfl

/-- The shape every reachable map has: `fmapEmpty`, or built with the lifted
    comparator and a nonzero insertion counter. -/
def Shaped (m : Fmap α β) : Prop :=
  m = fmapEmpty ∨
  ∃ (t : Std.TreeMap α (List (Nat × α × β)) (lemCmpToOrd c))
    (s : Std.TreeMap Nat (α × β)) (n : Nat),
      m = Fmap.mk (lemCmpToOrd c) t s n

theorem shaped_empty : Shaped c (fmapEmpty : Fmap α β) := .inl rfl

/-- Shape preservation: insert. -/
theorem shaped_add [BEq α] {m : Fmap α β} (h : Shaped c m) (k : α) (v : β) :
    Shaped c (fmapAddBy c k v m) := by
  rcases h with rfl | ⟨t, s, n, rfl⟩
  · exact .inr ⟨_, _, _, rfl⟩
  · exact .inr ⟨_, _, _, rfl⟩

/-- Shape preservation: delete. -/
theorem shaped_del [BEq α] {m : Fmap α β} (h : Shaped c m) (k : α) :
    Shaped c (fmapDeleteBy c k m) := by
  rcases h with rfl | ⟨t, s, n, rfl⟩
  · exact .inl rfl
  · simp only [fmapDeleteBy]
    cases Std.TreeMap.get? t k with
    | none => exact .inr ⟨_, _, _, rfl⟩
    | some bucket => exact .inr ⟨_, _, _, rfl⟩

/-- Characteristic lookup/insert law of the NEW implementation, for shaped
    maps. -/
theorem new_lookup_add [BEq α] [Std.TransCmp (lemCmpToOrd c)]
    {m : Fmap α β} (h : Shaped c m) (k k' : α) (v : β) :
    fmapLookupBy c k' (fmapAddBy c k v m) =
      if c k' k = .EQ then some v else fmapLookupBy c k' m := by
  rcases h with rfl | ⟨t, s, n, rfl⟩
  · -- fmapEmpty: comparator captured, fresh singleton tree
    show fmapLookupBy c k'
      (Fmap.mk (lemCmpToOrd c) (Std.TreeMap.empty.insert k [(0, k, v)])
        (Std.TreeMap.empty.insert 0 (k, v)) 1) = _
    simp only [fmapLookupBy, Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert]
    by_cases hEQ : c k' k = .EQ
    · rw [if_pos ((lemCmpToOrd_eq_iff c).mpr (cEq_symm c hEQ)), if_pos hEQ]
    · rw [if_neg (lemCmpToOrd_ne_eq c (fun hc => hEQ (cEq_symm c hc))), if_neg hEQ]
      rfl
  · -- built map: insert into the existing tree
    simp only [fmapAddBy, fmapLookupBy, Std.TreeMap.get?_eq_getElem?,
      Std.TreeMap.getElem?_insert]
    by_cases hEQ : c k' k = .EQ
    · rw [if_pos ((lemCmpToOrd_eq_iff c).mpr (cEq_symm c hEQ)), if_pos hEQ]
    · rw [if_neg (lemCmpToOrd_ne_eq c (fun hc => hEQ (cEq_symm c hc))), if_neg hEQ]

/-- Characteristic lookup/delete law of the NEW implementation, for shaped
    maps. -/
theorem new_lookup_del [BEq α] [Std.TransCmp (lemCmpToOrd c)]
    {m : Fmap α β} (h : Shaped c m) (k k' : α) :
    fmapLookupBy c k' (fmapDeleteBy c k m) =
      if c k' k = .EQ then none else fmapLookupBy c k' m := by
  rcases h with rfl | ⟨t, s, n, rfl⟩
  · -- fmapEmpty: delete is the identity, lookup is none either way
    cases hEQ : c k' k <;> rfl
  · simp only [fmapDeleteBy]
    cases hget : Std.TreeMap.get? t k with
    | none =>
      -- nothing cmp-EQ to k present; if k' is cmp-EQ to k its lookup is none too
      by_cases hEQ : c k' k = .EQ
      · have hcongr : Std.TreeMap.get? t k' = Std.TreeMap.get? t k := by
          simp only [Std.TreeMap.get?_eq_getElem?]
          exact Std.TreeMap.getElem?_congr
            ((lemCmpToOrd_eq_iff c).mpr hEQ)
        simp only [fmapLookupBy, hcongr, hget, if_pos hEQ]
      · simp only [fmapLookupBy, if_neg hEQ]
    | some bucket =>
      simp only [fmapLookupBy, Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_erase]
      by_cases hEQ : c k' k = .EQ
      · rw [if_pos ((lemCmpToOrd_eq_iff c).mpr (cEq_symm c hEQ)), if_pos hEQ]
      · rw [if_neg (lemCmpToOrd_ne_eq c (fun hc => hEQ (cEq_symm c hc))), if_neg hEQ]

/-- Scanning a filtered list equals scanning the original when every DROPPED
    entry could never match the scanned key. -/
theorem old_lookup_filter_irrel (k' : α) (f : α × β → Bool)
    (hf : ∀ p, f p = false → c k' p.1 ≠ .EQ) :
    ∀ l : LemLibLegacy.Fmap α β,
      LemLibLegacy.fmapLookupBy c k' (l.filter f) = LemLibLegacy.fmapLookupBy c k' l
  | [] => rfl
  | (pk, pv) :: rest => by
    by_cases hkeep : f (pk, pv) = true
    · simp only [List.filter_cons, hkeep, ite_true, LemLibLegacy.fmapLookupBy]
      cases hscan : c k' pk <;>
        simp [old_lookup_filter_irrel k' f hf rest]
    · have hkeep' : f (pk, pv) = false := by revert hkeep; cases f (pk, pv) <;> simp
      have hnomatch : c k' pk ≠ .EQ := hf (pk, pv) hkeep'
      simp only [List.filter_cons, hkeep', Bool.false_eq_true, ite_false]
      rw [old_lookup_filter_irrel k' f hf rest]
      cases hscan : c k' pk with
      | EQ => exact absurd hscan hnomatch
      | LT => simp [LemLibLegacy.fmapLookupBy, hscan]
      | GT => simp [LemLibLegacy.fmapLookupBy, hscan]

/-- Scanning a filtered list is `none` when every entry matching the scanned
    key is dropped. -/
theorem old_lookup_filter_none (k' : α) (f : α × β → Bool)
    (hf : ∀ p, c k' p.1 = .EQ → f p = false) :
    ∀ l : LemLibLegacy.Fmap α β,
      LemLibLegacy.fmapLookupBy c k' (l.filter f) = none
  | [] => rfl
  | (pk, pv) :: rest => by
    by_cases hkeep : f (pk, pv) = true
    · have hnomatch : c k' pk ≠ .EQ := by
        intro hmatch
        have := hf (pk, pv) hmatch
        simp [this] at hkeep
      simp only [List.filter_cons, hkeep, ite_true, LemLibLegacy.fmapLookupBy]
      cases hscan : c k' pk with
      | EQ => exact absurd hscan hnomatch
      | LT => simpa using old_lookup_filter_none k' f hf rest
      | GT => simpa using old_lookup_filter_none k' f hf rest
    · have hkeep' : f (pk, pv) = false := by revert hkeep; cases f (pk, pv) <;> simp
      simp only [List.filter_cons, hkeep', Bool.false_eq_true, ite_false]
      exact old_lookup_filter_none k' f hf rest

/-- Characteristic lookup/insert law of the RETIRED implementation, under
    BEq/comparator coherence. -/
theorem old_lookup_add [BEq α] [Std.TransCmp (lemCmpToOrd c)]
    (hBC : ∀ a b : α, (a == b) = true → c a b = .EQ)
    (l : LemLibLegacy.Fmap α β) (k k' : α) (v : β) :
    LemLibLegacy.fmapLookupBy c k' (LemLibLegacy.fmapAdd k v l) =
      if c k' k = .EQ then some v else LemLibLegacy.fmapLookupBy c k' l := by
  by_cases hEQ : c k' k = .EQ
  · simp [LemLibLegacy.fmapAdd, LemLibLegacy.fmapLookupBy, hEQ]
  · rw [if_neg hEQ]
    have head : LemLibLegacy.fmapLookupBy c k' (LemLibLegacy.fmapAdd k v l) =
        LemLibLegacy.fmapLookupBy c k' (l.filter (fun p => !(p.1 == k))) := by
      cases hscan : c k' k with
      | EQ => exact absurd hscan hEQ
      | LT => simp [LemLibLegacy.fmapAdd, LemLibLegacy.fmapLookupBy, hscan]
      | GT => simp [LemLibLegacy.fmapAdd, LemLibLegacy.fmapLookupBy, hscan]
    rw [head]
    refine old_lookup_filter_irrel c k' _ (fun p hp hmatch => ?_) l
    -- p was dropped: p.1 == k, so by coherence and EQ-transitivity k' matches k
    have hpk : (p.1 == k) = true := by
      revert hp; cases hbk : p.1 == k <;> simp
    exact hEQ (cEq_trans c hmatch (hBC _ _ hpk))

/-- Characteristic lookup/delete law of the RETIRED implementation. -/
theorem old_lookup_del [Std.TransCmp (lemCmpToOrd c)]
    (l : LemLibLegacy.Fmap α β) (k k' : α) :
    LemLibLegacy.fmapLookupBy c k' (LemLibLegacy.fmapDeleteBy c k l) =
      if c k' k = .EQ then none else LemLibLegacy.fmapLookupBy c k' l := by
  simp only [LemLibLegacy.fmapDeleteBy]
  by_cases hEQ : c k' k = .EQ
  · rw [if_pos hEQ]
    refine old_lookup_filter_none c k' _ (fun p hmatch => ?_) l
    -- every entry matching k' also matches k, hence is dropped
    have : c k p.1 = .EQ := cEq_trans c (cEq_symm c hEQ) hmatch
    simp [this]
  · rw [if_neg hEQ]
    refine old_lookup_filter_irrel c k' _ (fun p hp hmatch => ?_) l
    -- p was dropped: c k p.1 = EQ; then k' would match k — contradiction
    have hkp : c k p.1 = .EQ := by
      revert hp; cases hc : c k p.1 <;> simp
    exact hEQ (cEq_trans c hmatch (cEq_symm c hkp))

/-- MAIN THEOREM (lookup observable): for EVERY sequence of insert/delete
    operations, the new implementation and the retired reference return the
    same lookup result at every key — under comparator lawfulness
    (`TransCmp` of the lifted comparator) and BEq/comparator coherence. -/
theorem lookup_equiv [BEq α] [Std.TransCmp (lemCmpToOrd c)]
    (hBC : ∀ a b : α, (a == b) = true → c a b = .EQ)
    (ops : List (Op α β)) (k : α) :
    fmapLookupBy c k (applyNew c fmapEmpty ops) =
      LemLibLegacy.fmapLookupBy c k (applyOld c LemLibLegacy.fmapEmpty ops) := by
  suffices h : ∀ (ops : List (Op α β)) (m : Fmap α β) (l : LemLibLegacy.Fmap α β),
      Shaped c m →
      (∀ k, fmapLookupBy c k m = LemLibLegacy.fmapLookupBy c k l) →
      ∀ k, fmapLookupBy c k (applyNew c m ops) =
        LemLibLegacy.fmapLookupBy c k (applyOld c l ops) from
    h ops fmapEmpty LemLibLegacy.fmapEmpty (shaped_empty c) (fun _ => rfl) k
  intro ops
  induction ops with
  | nil => intro m l _ hagree k; exact hagree k
  | cons op rest ih =>
    intro m l hshape hagree k
    cases op with
    | add k0 v0 =>
      refine ih _ _ (shaped_add c hshape k0 v0) (fun k1 => ?_) k
      rw [new_lookup_add c hshape k0 k1 v0, old_lookup_add c hBC l k0 k1 v0]
      by_cases hEQ : c k1 k0 = .EQ <;> simp [hEQ, hagree k1]
    | del k0 =>
      refine ih _ _ (shaped_del c hshape k0) (fun k1 => ?_) k
      rw [new_lookup_del c hshape k0 k1, old_lookup_del c l k0 k1]
      by_cases hEQ : c k1 k0 = .EQ <;> simp [hEQ, hagree k1]

end Theorems

/- ========================================================================
   Bounded-exhaustive property tests: the observables whose bit-for-bit
   equivalence is not kernel-proved above (enumeration ORDER of
   `fmapElements`, isEmpty, domain, range, all, map, mapi, union, equalBy,
   ofSpine). EVERY operation sequence up to the stated depth is checked
   new-vs-old. `#guard` — failing any check fails the build.
   ======================================================================== -/

section PropertyTests

/-- Adversarial key type: derived BEq (both fields) is strictly finer than
    the comparator (first field only) — the cerberus `sym`/`identifier`
    situation; exercises the bucket machinery. -/
structure K2 where
  a : Nat
  b : Nat
  deriving BEq

def cK2 : K2 → K2 → LemOrdering := fun x y => defaultCompare x.a y.a
def cNat : Nat → Nat → LemOrdering := defaultCompare

/-- One op-alphabet step: add every key (position-stamped value) or delete
    every key. -/
def opChoices (keys : List α) (mkV : Nat → α → β) (step : Nat) : List (Op α β) :=
  keys.map (fun k => Op.add k (mkV step k)) ++ keys.map Op.del

/-- All op sequences of exactly the given length (values position-stamped,
    so any order mixup is observable). -/
def seqsOfLen (keys : List α) (mkV : Nat → α → β) : Nat → Nat → List (List (Op α β))
  | 0, _ => [[]]
  | n + 1, step =>
    (opChoices keys mkV step).flatMap (fun op =>
      (seqsOfLen keys mkV n (step + 1)).map (fun rest => op :: rest))

/-- All observables agree, new-vs-old — `fmapElements` comparison is
    order-sensitive (the spine bit-for-bit check). -/
def obsAgree [BEq α] [BEq β] (c : α → α → LemOrdering) (cv : β → β → LemOrdering)
    (keys : List α) (f : β → β) (g : α → β → β)
    (mN : Fmap α β) (mO : LemLibLegacy.Fmap α β) : Bool :=
  (fmapElements mN == LemLibLegacy.fmapElements mO)
  && keys.all (fun k => fmapLookupBy c k mN == LemLibLegacy.fmapLookupBy c k mO)
  && (fmapIsEmpty mN == LemLibLegacy.fmapIsEmpty mO)
  && (fmapDomainBy c mN == LemLibLegacy.fmapDomainBy c mO)
  && (fmapRangeBy cv mN == LemLibLegacy.fmapRangeBy cv mO)
  && (fmapAll (fun _ v => v == f v) mN == LemLibLegacy.fmapAll (fun _ v => v == f v) mO)
  && (fmapElements (fmapMap f mN) == LemLibLegacy.fmapElements (LemLibLegacy.fmapMap f mO))
  && (fmapElements (fmapMapi g mN) == LemLibLegacy.fmapElements (LemLibLegacy.fmapMapi g mO))

def checkSeqs [BEq α] [BEq β] (c : α → α → LemOrdering) (cv : β → β → LemOrdering)
    (keys : List α) (mkV : Nat → α → β) (f : β → β) (g : α → β → β) (len : Nat) : Bool :=
  (seqsOfLen keys mkV len 0).all (fun ops =>
    obsAgree c cv keys f g (applyNew c fmapEmpty ops) (applyOld c [] ops))

/-- Union and equalBy over all pairs of depth-2-built maps. -/
def checkPairs [BEq α] [BEq β] (c : α → α → LemOrdering)
    (keys : List α) (mkV : Nat → α → β) : Bool :=
  let seqs := seqsOfLen keys mkV 2 0
  seqs.all (fun o1 => seqs.all (fun o2 =>
    let n1 := applyNew c fmapEmpty o1
    let n2 := applyNew c fmapEmpty o2
    let l1 := applyOld c [] o1
    let l2 := applyOld c [] o2
    (fmapElements (fmapUnionBy c n1 n2)
        == LemLibLegacy.fmapElements (LemLibLegacy.fmapUnion l1 l2))
    && (fmapEqualBy (· == ·) (· == ·) n1 n2
        == LemLibLegacy.fmapEqualBy (· == ·) (· == ·) l1 l2)))

-- Nat keys (BEq = comparator-EQ), all op sequences of length ≤ 4
#guard checkSeqs cNat cNat [0, 1, 2] (fun s k => 100 * s + k) (· + 1) (fun k v => v + k) 0
#guard checkSeqs cNat cNat [0, 1, 2] (fun s k => 100 * s + k) (· + 1) (fun k v => v + k) 1
#guard checkSeqs cNat cNat [0, 1, 2] (fun s k => 100 * s + k) (· + 1) (fun k v => v + k) 2
#guard checkSeqs cNat cNat [0, 1, 2] (fun s k => 100 * s + k) (· + 1) (fun k v => v + k) 3
#guard checkSeqs cNat cNat [0, 1, 2] (fun s k => 100 * s + k) (· + 1) (fun k v => v + k) 4

-- Adversarial keys (BEq finer than comparator: buckets), length ≤ 4
#guard checkSeqs cK2 cNat [⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩] (fun s _ => s) (· + 1) (fun k v => v + k.b) 0
#guard checkSeqs cK2 cNat [⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩] (fun s _ => s) (· + 1) (fun k v => v + k.b) 1
#guard checkSeqs cK2 cNat [⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩] (fun s _ => s) (· + 1) (fun k v => v + k.b) 2
#guard checkSeqs cK2 cNat [⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩] (fun s _ => s) (· + 1) (fun k v => v + k.b) 3
#guard checkSeqs cK2 cNat [⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩] (fun s _ => s) (· + 1) (fun k v => v + k.b) 4

-- union / equalBy over all pairs of depth-2 maps, both key types
#guard checkPairs cNat [0, 1, 2] (fun s k => 100 * s + k)
#guard checkPairs cK2 [⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩] (fun s _ => s)

-- ofSpine roundtrip: elements of a rebuilt duplicate-free spine are the spine
#guard
  let spines : List (List (Nat × Nat)) :=
    [[], [(0, 10)], [(0, 10), (1, 11)], [(1, 11), (0, 10)],
     [(0, 10), (1, 11), (2, 12)], [(2, 12), (0, 10), (1, 11)]]
  spines.all (fun l => fmapElements (fmapOfSpine cNat l) == l)
#guard
  let spines : List (List (K2 × Nat)) :=
    [[(⟨0, 0⟩, 10), (⟨0, 1⟩, 11), (⟨1, 0⟩, 12)],
     [(⟨0, 1⟩, 11), (⟨1, 0⟩, 12), (⟨0, 0⟩, 10)]]
  spines.all (fun l => fmapElements (fmapOfSpine cK2 l) == l)

end PropertyTests

/- ========================================================================
   LemLibLegacy FREEZE-GUARD (arc-6 S5f, per audit-2).

   LemLibLegacy above is the retired reference implementation and the
   oracle for every theorem and property test in this file; if it drifts,
   the equivalence obligations silently stop meaning "new == retired".
   Mechanism chosen [AGENT:S5f]: characteristic-law #guards pinning
   Legacy's OWN behavior against hand-computed literals (the alternative
   — a recorded sha256 of the section checked by an external script —
   pins the text, but needs out-of-file wiring into the test flow and
   trips on harmless comment/whitespace edits; what the obligations
   actually need frozen is Legacy's SEMANTICS, and these guards break on
   exactly that: any behavioral drift of add's move-to-front + BEq-dedup,
   lookup's first-comparator-EQ scan, delete's comparator filter, union's
   left-fold-of-m2 direction, equalBy's two-sided find, or the
   BEq-finer-than-comparator split). Build-failing: `lake build` runs
   this file; a failing #guard is an elaboration error.
   ======================================================================== -/

section LegacyFreezeGuard

-- add = cons + BEq-filter: move-to-front, shadowed key removed, rest order kept
#guard LemLibLegacy.fmapAdd 1 20 [(2, 12), (1, 10), (3, 13)] == [(1, 20), (2, 12), (3, 13)]
-- add dedups EVERY BEq-equal occurrence, not just the first
#guard LemLibLegacy.fmapAdd 1 20 [(1, 10), (2, 12), (1, 11)] == [(1, 20), (2, 12)]
-- lookup = linear scan, FIRST comparator-EQ wins on a shadowed spine
#guard LemLibLegacy.fmapLookupBy cNat 1 [(1, 10), (1, 11)] == some 10
-- delete = comparator filter: removes ALL EQ entries, order-preserving
#guard LemLibLegacy.fmapDeleteBy cNat 1 [(2, 12), (1, 10), (3, 13), (1, 11)] == [(2, 12), (3, 13)]
-- BEq (finer) governs add's dedup; the comparator (coarser) governs
-- lookup/delete — the K2 bucket split the property tests rely on
#guard LemLibLegacy.fmapAdd (⟨0, 1⟩ : K2) 20 [(⟨0, 0⟩, 10)] == [(⟨0, 1⟩, 20), (⟨0, 0⟩, 10)]
#guard LemLibLegacy.fmapLookupBy cK2 ⟨0, 5⟩ [((⟨0, 1⟩ : K2), 20), (⟨0, 0⟩, 10)] == some 20
#guard LemLibLegacy.fmapDeleteBy cK2 ⟨0, 5⟩ [((⟨0, 1⟩ : K2), 20), (⟨1, 0⟩, 30), (⟨0, 0⟩, 10)]
  == [(⟨1, 0⟩, 30)]
-- union = m2 foldl-ed into m1 via fmapAdd: m2's later entries end frontmost...
#guard LemLibLegacy.fmapUnion [(1, 10)] [(2, 12), (3, 13)] == [(3, 13), (2, 12), (1, 10)]
-- ...and m2 overrides m1 on key collision
#guard LemLibLegacy.fmapUnion [(1, 10), (2, 12)] [(1, 20)] == [(1, 20), (2, 12)]
-- equalBy: two-sided find? check — value mismatch on a shadowed entry fails
#guard LemLibLegacy.fmapEqualBy (· == ·) (· == ·) [(1, 10), (1, 11)] [(1, 10)] == false
#guard LemLibLegacy.fmapEqualBy (· == ·) (· == ·) [(1, 10), (2, 12)] [(2, 12), (1, 10)] == true
-- domainBy = setFromListBy over keys: foldr dedup (keeps LAST duplicate's slot)
#guard LemLibLegacy.fmapDomainBy cNat [(2, 12), (1, 10), (3, 13)] == [2, 1, 3]
#guard LemLibLegacy.fmapDomainBy cNat [(2, 12), (1, 10), (2, 13)] == [1, 2]
#guard LemLibLegacy.fmapRangeBy cNat [(1, 12), (2, 10), (3, 12)] == [10, 12]
-- map/mapi/elements: spine order preserved; elements is the identity
#guard LemLibLegacy.fmapElements (LemLibLegacy.fmapMap (· + 1) [(2, 12), (1, 10)]) == [(2, 13), (1, 11)]
#guard LemLibLegacy.fmapMapi (fun k v => 10 * k + v) [(2, 1), (1, 3)] == [(2, 21), (1, 13)]
-- empty/isEmpty, incl. emptiness after add-then-delete
#guard LemLibLegacy.fmapIsEmpty (LemLibLegacy.fmapEmpty : LemLibLegacy.Fmap Nat Nat) == true
#guard LemLibLegacy.fmapIsEmpty
  (LemLibLegacy.fmapDeleteBy cNat 1 (LemLibLegacy.fmapAdd 1 10 LemLibLegacy.fmapEmpty)) == true
-- all: predicate sees both key and value
#guard LemLibLegacy.fmapAll (fun k v => k < v) [(1, 10), (2, 12)] == true
#guard LemLibLegacy.fmapAll (fun k v => k < v) [(1, 10), (12, 2)] == false

end LegacyFreezeGuard

/- ========================================================================
   Sum BEq/Ord parity pins (arc-10 S2 R1). Convention under test
   (LemLib.lean Sum instances): structural equality; inl < inr; payload
   order within a constructor — mirroring OCaml compare on
   Either.t/two-block variants (tags in declaration order, Left = 0).
   TESTS (untrusted-evaluator checks), not kernel proofs.
   ======================================================================== -/
section SumComparisonPins

#guard ((.inl 3 : Nat ⊕ Bool) == .inl 3) == true
#guard ((.inl 3 : Nat ⊕ Bool) == .inl 4) == false
#guard ((.inl 3 : Nat ⊕ Nat) == .inr 3) == false   -- cross-constructor: never equal
#guard ((.inr true : Nat ⊕ Bool) == .inr true) == true
#guard compare (.inl 9 : Nat ⊕ Nat) (.inr 0) == .lt   -- inl < inr regardless of payload
#guard compare (.inr 0 : Nat ⊕ Nat) (.inl 9) == .gt
#guard compare (.inl 3 : Nat ⊕ Bool) (.inl 4) == .lt
#guard compare (.inl 4 : Nat ⊕ Bool) (.inl 4) == .eq
#guard compare (.inr false : Nat ⊕ Bool) (.inr true) == .lt

end SumComparisonPins

end LemLibTest
