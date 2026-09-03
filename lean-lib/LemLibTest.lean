import LemLib
/-!
# LemLibTest — property tests for the `Pset`/`Pmap` ports

HISTORY: until the parity-fix slice (2026-09-03) this file carried the
arc-6 S3 Fmap representation-change obligations — the retired assoc-list
`Fmap` as a reference implementation, kernel-checked lookup-equivalence
theorems between it and the `Std.TreeMap`-indexed `Fmap`, and
bounded-exhaustive property tests — plus the arc-14 set-coherence
guards over the sorted-list set. Both representations are GONE: under
the [USER 2026-09-03] zero-discrepancy ruling the set and map
representations are verbatim ports of lem's OCaml runtime AVL trees
(ocaml-lib/pset.ml, pmap.ml; see the LemLib.lean section header), whose
specification is the OCaml code itself. The load-bearing evidence is
therefore the TWO-TARGET parity suite (tests/comprehensive/parity/,
probes p_set_ops / p_map_ops / p_map_beq / p_cmp_order / p_show: an
OCaml binary and a Lean binary built from the same lem source, outputs
byte-identical). This file keeps the Lean-internal sanity net that a
parity run cannot express: the AVL representation invariants after
bounded-exhaustive operation sequences (with adversarial keys whose
derived BEq is finer than the comparator), and a handful of
kernel-checked examples of the OCaml-specific observables the port
exists to reproduce. Building it IS running it: every `#guard` is
evaluated at elaboration time and a false one fails the build.
-/

namespace LemLibTest

/-! ## Adversarial key: derived BEq finer than the comparator -/

structure K2 where
  a : Nat
  b : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Comparator on the first component only: `⟨0,0⟩ ~ ⟨0,1⟩`. -/
def cK2 : K2 → K2 → LemOrdering := fun x y => defaultCompare x.a y.a
def cNat : Nat → Nat → LemOrdering := defaultCompare

/-! ## Representation invariants (pset.ml's documented ones) -/

/-- Heights consistent and AVL-balanced (children differ by at most 2,
    as the OCaml comment states). -/
def Pset.wellFormed : Pset α → Bool
  | .Empty => true
  | .Node l _ r h =>
    let hl := Pset.height l
    let hr := Pset.height r
    h == (if hl >= hr then hl + 1 else hr + 1) && (hl + 2 >= hr) && (hr + 2 >= hl) &&
    Pset.wellFormed l && Pset.wellFormed r

/-- Strictly ascending in-order traversal (no comparator-EQ duplicates). -/
def strictlyAscending (cmp : α → α → LemOrdering) : List α → Bool
  | [] | [_] => true
  | x :: y :: rest => (match cmp x y with | .LT => true | _ => false) && strictlyAscending cmp (y :: rest)

def Pmap.wellFormed : Pmap α β → Bool
  | .Empty => true
  | .Node l _ _ r h =>
    let hl := Pmap.height l
    let hr := Pmap.height r
    h == (if hl >= hr then hl + 1 else hr + 1) && (hl + 2 >= hr) && (hr + 2 >= hl) &&
    Pmap.wellFormed l && Pmap.wellFormed r

/-! ## Bounded-exhaustive operation sequences -/

inductive SOp (α : Type) where
  | add (x : α)
  | remove (x : α)
  | unionWith (l : List α)
  | interWith (l : List α)
  | diffWith (l : List α)
  | filterEven

def applySOp (cmp : K2 → K2 → LemOrdering) (s : Pset K2) : SOp K2 → Pset K2
  | .add x => Pset.add cmp x s
  | .remove x => Pset.remove cmp x s
  | .unionWith l => Pset.union cmp s (Pset.fromList cmp l)
  | .interWith l => Pset.inter cmp s (Pset.fromList cmp l)
  | .diffWith l => Pset.diff cmp s (Pset.fromList cmp l)
  | .filterEven => Pset.filter cmp (fun k => k.a % 2 == 0) s

def pool : List K2 := [⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 1⟩, ⟨4, 0⟩, ⟨5, 0⟩, ⟨6, 1⟩]

def opChoices : List (SOp K2) :=
  (pool.map SOp.add) ++ (pool.map SOp.remove) ++
  [SOp.unionWith [⟨1, 1⟩, ⟨7, 0⟩, ⟨0, 1⟩], SOp.interWith [⟨0, 1⟩, ⟨2, 1⟩, ⟨5, 5⟩],
   SOp.diffWith [⟨1, 0⟩, ⟨4, 4⟩], SOp.filterEven]

/-- All sequences of exactly `n` ops (|opChoices|^n of them). -/
def seqs : Nat → List (List (SOp K2))
  | 0 => [[]]
  | n + 1 => (seqs n).flatMap fun s => opChoices.map fun o => o :: s

def runSeq (s : List (SOp K2)) : Pset K2 := s.foldl (applySOp cK2) .Empty

/-- Invariant check over every sequence: well-formed, strictly ascending
    elements, cardinal = length of elements, membership agrees with the
    element list, and equality with itself. -/
def setInvariantsHold (s : Pset K2) : Bool :=
  let es := Pset.elements s
  Pset.wellFormed s && strictlyAscending cK2 es && Pset.cardinal s == es.length &&
  pool.all (fun k => Pset.mem cK2 k s == es.any (fun e => match cK2 e k with | .EQ => true | _ => false)) &&
  Pset.equal cK2 s s && Pset.subset cK2 s s

#guard (seqs 3).all (fun ops => setInvariantsHold (runSeq ops))   -- 20^3 = 8000 sequences

/-! ## Map invariants over op sequences -/

inductive MOp where
  | add (k : K2) (v : Nat)
  | remove (k : K2)
  | unionWith (l : List (K2 × Nat))

def applyMOp (m : Pmap K2 Nat) : MOp → Pmap K2 Nat
  | .add k v => Pmap.add cK2 k v m
  | .remove k => Pmap.remove cK2 k m
  | .unionWith l => Pmap.union cK2 m (l.foldl (fun acc (k, v) => Pmap.add cK2 k v acc) .Empty)

def mopChoices : List MOp :=
  (pool.map fun k => MOp.add k k.b) ++ (pool.map MOp.remove) ++
  [MOp.unionWith [(⟨1, 1⟩, 9), (⟨7, 0⟩, 8)], MOp.unionWith [(⟨0, 1⟩, 7)]]

def mseqs : Nat → List (List MOp)
  | 0 => [[]]
  | n + 1 => (mseqs n).flatMap fun s => mopChoices.map fun o => o :: s

def mapInvariantsHold (m : Pmap K2 Nat) : Bool :=
  let bs := Pmap.bindings m
  Pmap.wellFormed m && strictlyAscending cK2 (bs.map Prod.fst) && Pmap.cardinal m == bs.length &&
  pool.all (fun k => (Pmap.find? cK2 k m).isSome == bs.any (fun (k', _) => match cK2 k' k with | .EQ => true | _ => false)) &&
  Pmap.equal cK2 (fun a b => a == b) m m

#guard (mseqs 3).all (fun ops => mapInvariantsHold (ops.foldl applyMOp .Empty))   -- 18^3 = 5832 sequences

/-! ## Kernel-checked examples of the OCaml observables the port reproduces -/

/-- Pmap.add REPLACES a comparator-equal binding — new key and new value
    (F3; pmap.ml:67-73): the noodle probe p_map_beq shape. -/
example : Pmap.bindings (Pmap.add cK2 ⟨1, 0⟩ 1 (Pmap.add cK2 ⟨1, 1⟩ 2 .Empty)) = [(⟨1, 0⟩, 1)] := by decide

/-- Pset.add keeps the FIRST comparator-equal element (pset.ml:76-80). -/
example : Pset.elements (Pset.add cK2 ⟨1, 0⟩ (Pset.add cK2 ⟨1, 1⟩ .Empty)) = [⟨1, 1⟩] := by decide

/-- Iteration is ascending by the comparator, whatever the insertion order. -/
example : Pset.elements (Pset.fromList cNat [3, 1, 2]) = [1, 2, 3] := by decide
example : Pmap.bindings ((Pmap.add cNat 3 "c" (Pmap.add cNat 1 "a" (Pmap.add cNat 2 "b" .Empty)))) =
    [(1, "a"), (2, "b"), (3, "c")] := by decide

/-- `fold` is ascending (pset.ml:254): folding cons yields the reversed list. -/
example : Pset.fold (fun x acc => x :: acc) (Pset.fromList cNat [2, 3, 1]) [] = [3, 2, 1] := by decide

/-- Pmap.equal compares keys with the map's comparator and IGNORES lem's
    key equality (pmap.ml:253-261, 296): the F3 `m1 = m2` row. -/
example : fmapEqualBy (fun (a b : K2) => a == b) (fun a b => a == b)
    (fmapAddBy cK2 ⟨1, 0⟩ 1 fmapEmpty) (fmapAddBy cK2 ⟨1, 1⟩ 1 fmapEmpty) = true := by decide

/-- set_case sees a singleton by its exact shape (pset.ml:360). -/
example : Pset.setCase (Pset.fromList cNat [5]) "e" (fun _ => "s") "m" = "s" := by decide
example : Pset.setCase (Pset.fromList cNat [5, 6]) "e" (fun _ => "s") "m" = "m" := by decide

/-- `lean_box(0)` ABI: the empty set / map is the first nullary constructor. -/
example : (setEmpty : Pset Nat) = Pset.Empty := rfl
example : (fmapEmpty : Fmap Nat Nat) = Fmap.empty := rfl

end LemLibTest
