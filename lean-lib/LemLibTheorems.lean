import LemLib
/-!
# LemLibTheorems — kernel-checked equalities for the tail-recursive
library rewrites (parity-fix slice 2026-09-03, F7)

Agreement between Lean artifacts is a theorem, not a test. Each
`lemList*`/`lemString*`/`lemInsertBy` function in `LemLib.lean` replaces
a definition that overflowed the native stack on 300 000-element inputs
(the compiled sweep in the parity-fix record); this file restates the
REPLACED definition verbatim as a `spec` (the core function itself for
`List.zip`/`List.unzip`/`List.foldr`; the generated lem text for the
library definitions) and proves the rewrite equal to it, by canonical
list induction generalising the accumulator. Built with the library
(`lake build` in lean-lib): a failing proof fails the build.

Cones: every theorem here is closed under `propext`, `Classical.choice`
and `Quot.sound` at most (the three standard axioms) — no `sorry`, no
`native_decide`, no `ofReduce*`; check with `#print axioms`.

NOT PROVED (recorded, STOP-AND-REPORT class): `lemListUnfoldr` replaces
a `partial def` (lem `List_extra.unfoldr` is non-terminating in
general); a `partial` definition is opaque to the kernel on both sides,
so no equality theorem can be stated. The rewrite is the same recursion
with an accumulator; its only witness is the two-target parity run.
-/

namespace LemLibTheorems
variable {α β : Type}

/- ---- List.zip ---- -/
theorem lemListZipAux_eq (l1 : List α) (l2 : List β) (acc : List (α × β)) :
    lemListZipAux l1 l2 acc = acc.reverse ++ List.zip l1 l2 := by
  induction l1 generalizing l2 acc with
  | nil => cases l2 <;> simp [lemListZipAux]
  | cons x xs ih =>
    cases l2 with
    | nil => simp [lemListZipAux]
    | cons y ys => simp [lemListZipAux, ih]

theorem lemListZip_eq (l1 : List α) (l2 : List β) : lemListZip l1 l2 = List.zip l1 l2 := by
  simp [lemListZip, lemListZipAux_eq]

/- ---- List.unzip ---- -/
theorem lemListUnzipAux_eq (l : List (α × β)) (as : List α) (bs : List β) :
    lemListUnzipAux l as bs = (as.reverse ++ (List.unzip l).1, bs.reverse ++ (List.unzip l).2) := by
  induction l generalizing as bs with
  | nil => simp [lemListUnzipAux]
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    simp [lemListUnzipAux, ih, List.unzip_cons]

theorem lemListUnzip_eq (l : List (α × β)) : lemListUnzip l = List.unzip l := by
  simp [lemListUnzip, lemListUnzipAux_eq, List.unzip_eq_map]

/- ---- List.foldr ---- -/
theorem lemListFoldr_eq (f : α → β → β) (init : β) (l : List α) :
    lemListFoldr f init l = List.foldr f init l := by
  simp [lemListFoldr]

/- ---- lem List.deleteFirst (generated Lem_List.deleteFirst, verbatim) ---- -/
def deleteFirstSpec (P : α → Bool) (l : List α) : Option (List α) :=
  match l with
  | [] => none
  | x :: xs => if P x then some xs else Option.map (fun xs' => x :: xs') (deleteFirstSpec P xs)

theorem lemListDeleteFirstAux_eq (P : α → Bool) (l acc : List α) :
    lemListDeleteFirstAux P l acc = Option.map (fun r => acc.reverse ++ r) (deleteFirstSpec P l) := by
  induction l generalizing acc with
  | nil => simp [lemListDeleteFirstAux, deleteFirstSpec]
  | cons x xs ih =>
    simp only [lemListDeleteFirstAux, deleteFirstSpec]
    split
    · simp [List.reverseAux_eq]
    · rw [ih]
      cases deleteFirstSpec P xs <;> simp

theorem lemListDeleteFirst_eq (P : α → Bool) (l : List α) :
    lemListDeleteFirst P l = deleteFirstSpec P l := by
  simp [lemListDeleteFirst, lemListDeleteFirstAux_eq]

/- ---- lem List.update (generated Lem_List.update, verbatim) ---- -/
def updateSpec (l : List α) (n : Nat) (e : α) : List α :=
  match l with
  | [] => []
  | x :: xs => if n == 0 then e :: xs else x :: updateSpec xs (n - 1) e

theorem lemListUpdateAux_eq (e : α) (l : List α) (n : Nat) (acc : List α) :
    lemListUpdateAux e l n acc = acc.reverse ++ updateSpec l n e := by
  induction l generalizing n acc with
  | nil => simp [lemListUpdateAux, updateSpec]
  | cons x xs ih =>
    simp only [lemListUpdateAux, updateSpec]
    split
    · simp [List.reverseAux_eq]
    · simp [ih]

theorem lemListUpdate_eq (l : List α) (n : Nat) (e : α) : lemListUpdate l n e = updateSpec l n e := by
  simp [lemListUpdate, lemListUpdateAux_eq]

/- ---- lem List.catMaybes (generated Lem_List.catMaybes, verbatim) ---- -/
def catMaybesSpec : List (Option α) → List α
  | [] => []
  | none :: xs' => catMaybesSpec xs'
  | some x :: xs' => x :: catMaybesSpec xs'

theorem lemListCatMaybesAux_eq (xs : List (Option α)) (acc : List α) :
    lemListCatMaybesAux xs acc = acc.reverse ++ catMaybesSpec xs := by
  induction xs generalizing acc with
  | nil => simp [lemListCatMaybesAux, catMaybesSpec]
  | cons o xs ih => cases o <;> simp [lemListCatMaybesAux, catMaybesSpec, ih]

theorem lemListCatMaybes_eq (xs : List (Option α)) : lemListCatMaybes xs = catMaybesSpec xs := by
  simp [lemListCatMaybes, lemListCatMaybesAux_eq]

/- ---- lem List.mapiAux / mapi (generated, verbatim) ---- -/
def mapiAuxSpec (f : Nat → α → β) (n : Nat) : List α → List β
  | [] => []
  | x :: xs => f n x :: mapiAuxSpec f (n + 1) xs

theorem lemListMapiAuxAcc_eq (f : Nat → α → β) (n : Nat) (l : List α) (acc : List β) :
    lemListMapiAuxAcc f n l acc = acc.reverse ++ mapiAuxSpec f n l := by
  induction l generalizing n acc with
  | nil => simp [lemListMapiAuxAcc, mapiAuxSpec]
  | cons x xs ih => simp [lemListMapiAuxAcc, mapiAuxSpec, ih]

theorem lemListMapiAux_eq (f : Nat → α → β) (n : Nat) (l : List α) :
    lemListMapiAux f n l = mapiAuxSpec f n l := by
  simp [lemListMapiAux, lemListMapiAuxAcc_eq]

theorem lemListMapi_eq (f : Nat → α → β) (l : List α) : lemListMapi f l = mapiAuxSpec f 0 l := by
  simp [lemListMapi, lemListMapiAuxAcc_eq]

/- ---- lem List_extra.init (generated Lem_List_extra.init, verbatim) ---- -/
def initSpec : List α → List α
  | [_] => []
  | x1 :: x2 :: xs => x1 :: initSpec (x2 :: xs)
  | [] => failwithI "List_extra.init of empty list"

theorem lemListInitAux_eq (x : α) (xs acc : List α) :
    lemListInitAux (x :: xs) acc = acc.reverse ++ initSpec (x :: xs) := by
  induction xs generalizing x acc with
  | nil => simp [lemListInitAux, initSpec]
  | cons x2 xs ih => simp [lemListInitAux, initSpec, ih]

theorem lemListInit_eq (l : List α) : lemListInit l = initSpec l := by
  cases l with
  | nil => simp [lemListInit, initSpec]
  | cons x xs => simp [lemListInit, lemListInitAux_eq]

/- ---- lem List_extra.zipSameLength (generated, verbatim) ----
   The success domain (equal lengths) is the theorem; on unequal lengths
   both definitions reach `failwithI` with the same message (the spec
   conses a prefix onto the opaque failure value, the rewrite returns it
   directly — both PANIC there, which is the property that matters under
   exception class (a); as values the two cannot be equated because
   failwithI is opaque). -/
def zipSameLengthSpec : List α → List β → List (α × β)
  | x :: xs, y :: ys => (x, y) :: zipSameLengthSpec xs ys
  | [], [] => []
  | _, _ => failwithI "List_extra.zipSameLength of different length lists"

theorem lemListZipSameLengthAux_eq (l1 : List α) (l2 : List β) (acc : List (α × β))
    (h : l1.length = l2.length) :
    lemListZipSameLengthAux l1 l2 acc = acc.reverse ++ zipSameLengthSpec l1 l2 := by
  induction l1 generalizing l2 acc with
  | nil => cases l2 with
    | nil => simp [lemListZipSameLengthAux, zipSameLengthSpec]
    | cons _ _ => simp at h
  | cons x xs ih => cases l2 with
    | nil => simp at h
    | cons y ys =>
      simp at h
      simp [lemListZipSameLengthAux, zipSameLengthSpec, ih ys _ h]

theorem lemListZipSameLength_eq (l1 : List α) (l2 : List β) (h : l1.length = l2.length) :
    lemListZipSameLength l1 l2 = zipSameLengthSpec l1 l2 := by
  simp [lemListZipSameLength, lemListZipSameLengthAux_eq l1 l2 [] h]

/- ---- lem Sorting.insertBy (generated Lem_Sorting.insertBy, verbatim) ---- -/
def insertBySpec (cmp : α → α → Bool) (e : α) : List α → List α
  | [] => [e]
  | x :: xs => if cmp x e then x :: insertBySpec cmp e xs else e :: x :: xs

theorem lemInsertByAux_eq (cmp : α → α → Bool) (e : α) (l acc : List α) :
    lemInsertByAux cmp e l acc = acc.reverse ++ insertBySpec cmp e l := by
  induction l generalizing acc with
  | nil => simp [lemInsertByAux, insertBySpec, List.reverseAux_eq]
  | cons x xs ih =>
    simp only [lemInsertByAux, insertBySpec]
    split
    · simp [ih]
    · simp [List.reverseAux_eq]

theorem lemInsertBy_eq (cmp : α → α → Bool) (e : α) (l : List α) :
    lemInsertBy cmp e l = insertBySpec cmp e l := by
  simp [lemInsertBy, lemInsertByAux_eq]

/- ---- lem String.concat (generated Lem_String.concat, verbatim) and
        Show.stringFromListAux (the same recursion with sep = "; ") ---- -/
def concatSpec (sep : String) : List String → String
  | [] => ""
  | s :: ss' => match ss' with
    | [] => s
    | _ => String.append s (String.append sep (concatSpec sep ss'))

/-- `String.append` IS `++` on strings (the generated text spells the
    function name; the rewrite uses the notation). -/
theorem string_append_eq (a b : String) : String.append a b = a ++ b := rfl

theorem lemStringJoinAux_eq (sep : String) (ss : List String) (acc : String) :
    lemStringJoinAux sep ss acc = (match ss with | [] => acc | _ => acc ++ sep ++ concatSpec sep ss) := by
  induction ss generalizing acc with
  | nil => simp [lemStringJoinAux]
  | cons s ss ih =>
    simp only [lemStringJoinAux]
    rw [ih]
    cases ss with
    | nil => simp [concatSpec]
    | cons t ts => simp [concatSpec, string_append_eq, String.append_assoc]

theorem lemStringConcat_eq (sep : String) (ss : List String) : lemStringConcat sep ss = concatSpec sep ss := by
  cases ss with
  | nil => simp [lemStringConcat, lemStringJoin, concatSpec]
  | cons s ss =>
    simp only [lemStringConcat, lemStringJoin]
    rw [lemStringJoinAux_eq]
    cases ss <;> simp [concatSpec, string_append_eq, String.append_assoc]

def stringFromListAuxSpec (showX : α → String) : List α → String
  | [] => ""
  | x :: xs' => match xs' with
    | [] => showX x
    | _ => String.append (showX x) (String.append "; " (stringFromListAuxSpec showX xs'))

theorem concatSpec_map (showX : α → String) : ∀ (xs : List α),
    concatSpec "; " (xs.map showX) = stringFromListAuxSpec showX xs
  | [] => by simp [concatSpec, stringFromListAuxSpec]
  | [x] => by simp [concatSpec, stringFromListAuxSpec]
  | x :: y :: ys => by
    have ih := concatSpec_map showX (y :: ys)
    show (showX x).append ("; ".append (concatSpec "; " (List.map showX (y :: ys)))) =
         (showX x).append ("; ".append (stringFromListAuxSpec showX (y :: ys)))
    rw [ih]

theorem lemShowListAux_eq (showX : α → String) (xs : List α) :
    lemShowListAux showX xs = stringFromListAuxSpec showX xs := by
  simp only [lemShowListAux]
  rw [show lemStringJoin "; " (xs.map showX) = lemStringConcat "; " (xs.map showX) from rfl,
      lemStringConcat_eq, concatSpec_map]

/- ---- Pset.join / Pmap.join: height-indexed structural recursion vs the
        former well-founded definition (fuel-parameter arc, 2026-09-04) ----
   `joinSpec` is the pre-arc text verbatim (WF on `sizeOf l + sizeOf r`).
   The two agree on every pair of heights-consistent trees (`heightsOk`):
   the index `height l + height r + 1` then exceeds the recursion depth,
   because each step descends into a child of the taller side whose stored
   height is strictly smaller. Without `heightsOk` the stored heights may
   lie and the indexed version reaches its (loud) exhaustion arm where the
   WF version keeps going — so the hypothesis is exactly the invariant
   every constructor path preserves (the consumer's Pmap-laws slice will
   prove that preservation against these same definitions). -/
namespace PsetJoin
open Pset
variable {α : Type}

def joinSpec (cmp : α → α → LemOrdering) (l : Pset α) (v : α) (r : Pset α) : Pset α :=
  match l, r with
  | .Empty, _ => add cmp v r
  | _, .Empty => add cmp v l
  | .Node ll lv lr lh, .Node rl rv rr rh =>
    if lh > rh + 2 then bal ll lv (joinSpec cmp lr v (.Node rl rv rr rh))
    else if rh > lh + 2 then bal (joinSpec cmp (.Node ll lv lr lh) v rl) rv rr
    else create l v r
termination_by sizeOf l + sizeOf r
decreasing_by all_goals simp_wf <;> omega

theorem heightsOk_node {l r : Pset α} {v : α} {h : Nat} (hk : heightsOk (.Node l v r h) = true) :
    h = (if height l >= height r then height l + 1 else height r + 1) ∧
    heightsOk l = true ∧ heightsOk r = true := by
  simp only [heightsOk, Bool.and_eq_true, beq_iff_eq] at hk
  exact ⟨hk.1.1, hk.1.2, hk.2⟩

theorem joinGo_eq (cmp : α → α → LemOrdering) (v : α) :
    ∀ (n : Nat) (l r : Pset α), heightsOk l = true → heightsOk r = true →
      height l + height r < n → joinGo cmp n l v r = joinSpec cmp l v r := by
  intro n
  induction n with
  | zero => intro l r _ _ hn; omega
  | succ n ih =>
    intro l r hl hr hn
    cases l with
    | Empty => cases r <;> simp [joinGo, joinSpec]
    | Node ll lv lr lh =>
      cases r with
      | Empty => simp [joinGo, joinSpec]
      | Node rl rv rr rh =>
        obtain ⟨hlh, hll, hlr⟩ := heightsOk_node hl
        obtain ⟨hrh, hrl, hrr⟩ := heightsOk_node hr
        simp only [joinGo, joinSpec]
        simp only [height] at hn
        split
        · -- lh > rh + 2: descend into lr (its stored height is below lh)
          rw [ih lr (.Node rl rv rr rh) hlr hr]
          have h1 : height lr < lh := by rw [hlh]; split <;> omega
          show height lr + rh < n; omega
        · split
          · -- rh > lh + 2: descend into rl
            rw [ih (.Node ll lv lr lh) rl hl hrl]
            have h1 : height rl < rh := by rw [hrh]; split <;> omega
            show lh + height rl < n; omega
          · rfl

theorem join_eq (cmp : α → α → LemOrdering) (l : Pset α) (v : α) (r : Pset α)
    (hl : heightsOk l = true) (hr : heightsOk r = true) :
    join cmp l v r = joinSpec cmp l v r :=
  joinGo_eq cmp v _ l r hl hr (by omega)

end PsetJoin

namespace PmapJoin
open Pmap
variable {α β : Type}

def joinSpec (cmp : α → α → LemOrdering) (l : Pmap α β) (v : α) (d : β) (r : Pmap α β) : Pmap α β :=
  match l, r with
  | .Empty, _ => add cmp v d r
  | _, .Empty => add cmp v d l
  | .Node ll lv ld lr lh, .Node rl rv rd rr rh =>
    if lh > rh + 2 then bal ll lv ld (joinSpec cmp lr v d (.Node rl rv rd rr rh))
    else if rh > lh + 2 then bal (joinSpec cmp (.Node ll lv ld lr lh) v d rl) rv rd rr
    else create l v d r
termination_by sizeOf l + sizeOf r
decreasing_by all_goals simp_wf <;> omega

theorem heightsOk_node {l r : Pmap α β} {v : α} {d : β} {h : Nat}
    (hk : heightsOk (.Node l v d r h) = true) :
    h = (if height l >= height r then height l + 1 else height r + 1) ∧
    heightsOk l = true ∧ heightsOk r = true := by
  simp only [heightsOk, Bool.and_eq_true, beq_iff_eq] at hk
  exact ⟨hk.1.1, hk.1.2, hk.2⟩

theorem joinGo_eq (cmp : α → α → LemOrdering) (v : α) (d : β) :
    ∀ (n : Nat) (l r : Pmap α β), heightsOk l = true → heightsOk r = true →
      height l + height r < n → joinGo cmp n l v d r = joinSpec cmp l v d r := by
  intro n
  induction n with
  | zero => intro l r _ _ hn; omega
  | succ n ih =>
    intro l r hl hr hn
    cases l with
    | Empty => cases r <;> simp [joinGo, joinSpec]
    | Node ll lv ld lr lh =>
      cases r with
      | Empty => simp [joinGo, joinSpec]
      | Node rl rv rd rr rh =>
        obtain ⟨hlh, hll, hlr⟩ := heightsOk_node hl
        obtain ⟨hrh, hrl, hrr⟩ := heightsOk_node hr
        simp only [joinGo, joinSpec]
        simp only [height] at hn
        split
        · rw [ih lr (.Node rl rv rd rr rh) hlr hr]
          have h1 : height lr < lh := by rw [hlh]; split <;> omega
          show height lr + rh < n; omega
        · split
          · rw [ih (.Node ll lv ld lr lh) rl hl hrl]
            have h1 : height rl < rh := by rw [hrh]; split <;> omega
            show lh + height rl < n; omega
          · rfl

theorem join_eq (cmp : α → α → LemOrdering) (l : Pmap α β) (v : α) (d : β) (r : Pmap α β)
    (hl : heightsOk l = true) (hr : heightsOk r = true) :
    join cmp l v d r = joinSpec cmp l v d r :=
  joinGo_eq cmp v d _ l r hl hr (by omega)

end PmapJoin

end LemLibTheorems

#print axioms LemLibTheorems.PsetJoin.join_eq
#print axioms LemLibTheorems.PmapJoin.join_eq
#print axioms LemLibTheorems.lemListZip_eq
#print axioms LemLibTheorems.lemListUnzip_eq
#print axioms LemLibTheorems.lemListFoldr_eq
#print axioms LemLibTheorems.lemListDeleteFirst_eq
#print axioms LemLibTheorems.lemListUpdate_eq
#print axioms LemLibTheorems.lemListCatMaybes_eq
#print axioms LemLibTheorems.lemListMapi_eq
#print axioms LemLibTheorems.lemListInit_eq
#print axioms LemLibTheorems.lemListZipSameLength_eq
#print axioms LemLibTheorems.lemInsertBy_eq
#print axioms LemLibTheorems.lemStringConcat_eq
#print axioms LemLibTheorems.lemShowListAux_eq
