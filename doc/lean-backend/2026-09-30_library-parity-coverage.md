# Library parity coverage — record (2026-09-30)

Branch `linksem/lib-probes` (from `linksem/fixes` at `18f6ef7`), worktree
`linksem-lean/worktrees/lem-lib-probes`. Charter (orchestrator, linksem
port): extend the two-target parity lane (`tests/comprehensive/parity/`)
to cover Lem's standard library systematically and find where LemLib
(generated from `library/*.lem` by the Lean backend, plus
`lean-lib/LemLib.lean`) computes something different from the OCaml
library (`ocaml-lib/`). Worker [AGENT]; nothing pushed, nothing merged.

Reference semantics: the OCaml target, except OCaml's hard-coded machine
limits ([USER 2026-09-03], `2026-09-03_exception-case-rulings.md`: the
63-bit `nat`/`int` wrap and the raising `int_of_big_int`/`int32_of_big_int`
conversions are deviations; the logical semantics wins there).

## 0. Commits

| Commit | Content |
|---|---|
| `5322853` | LemLib fixes LP3, LP4, LP6, LP7, LP8 with their regression probes (`p_lib_word_int_nat`, `p_lib_machine_word`, `f_lib_chr_range`), `test_mword.lem` asserts, LemLibTest kernel examples, nonlean goldens (comment/declare-only drift) |
| (this record's commit) | the coverage tool, the remaining `p_lib_*`/`f_lib_*` probes and pins, this record |

## 1. Coverage — method and numbers

Tool: `tests/comprehensive/parity/tools/lib_coverage.py` (fails on an empty
library/probe set; `--list-uncovered` lists names). Metric [AGENT]:

- a named `val` of `library/*.lem` is ELIGIBLE if it has an OCaml AND a
  Lean realisation: a `declare <targets> target_rep function`, a
  `let`/`and` definition whose target set admits the target, or a class
  method. A val whose type mentions `rational`/`real`/`float64`/`float32`,
  or whose Lean rep is a `LemUnsupported.` refusal, has no Lean
  realisation (exception class (c)). Operators (`val (+)`) are not counted.
- it is COVERED if its name occurs in a probe (comments stripped); a name
  declared in several modules counts only when qualified (`Set.null`).
  Class-dispatched uses (`+` at nat reaching `natAdd`) do not count —
  the new probes call the named functions directly for that reason.

| module | eligible | before | after |
|---|---:|---:|---:|
| Assert_extra | 3 | 1 | 3 |
| Basic_classes | 29 | 3 | 29 |
| Bool | 2 | 1 | 2 |
| Either | 8 | 1 | 8 |
| Function | 6 | 1 | 6 |
| Function_extra | 1 | 0 | 0 |
| List | 59 | 24 | 59 |
| List_extra | 10 | 3 | 10 |
| Machine_word | 43 | 1 | 40 |
| Map | 23 | 18 | 23 |
| Map_extra | 5 | 4 | 5 |
| Maybe | 8 | 2 | 8 |
| Maybe_extra | 1 | 0 | 1 |
| Num | 146 | 24 | 139 |
| Num_extra | 7 | 5 | 7 |
| Relation | 44 | 1 | 44 |
| Set | 38 | 21 | 38 |
| Set_extra | 7 | 5 | 7 |
| Set_helpers | 1 | 1 | 1 |
| Show | 5 | 1 | 5 |
| Sorting | 12 | 2 | 12 |
| String | 8 | 7 | 8 |
| String_extra | 11 | 8 | 11 |
| Tuple | 5 | 1 | 5 |
| Word | 87 | 20 | 86 |
| **total** | **569** | **155** | **557** |

(Debug, Transform, Pervasives, Pervasives_extra, Show_extra: 0 eligible.)
The orchestrator's rough pre-scan (186 of 703) counted differently
(ineligible vals included, unqualified names matched in any module).

Probes added (all green; OCaml pins generated with `REBASELINE=1`, then
reviewed): `p_lib_misc` (Basic_classes, Bool, Either, Function, Tuple,
Maybe, Show helpers, Sorting, List_extra, String, String_extra, Num_extra,
Set_extra, Map_extra; 142 lines), `p_lib_num_nat_int` (2205),
`p_lib_num_big` (natural/integer, 3024), `p_lib_num_fixed` (int32/int64 and
the conversions, 2076), `p_lib_word` (bitSequence + integer/natural/int32/
int64 bitwise, 426), `p_lib_word_int_nat` (459), `p_lib_machine_word` (512),
`p_lib_relation` (54), `p_lib_list` (96), `p_lib_set_map` (49), and 17
failure probes `f_lib_*` (head/tail/init/last/foldl1 of [], nth and
String_extra.nth out of range, findNonPure without match, zipSameLength
on unequal lists, fromJust Nothing, Map_extra.find absent, Set_extra.choose
of {}, failwith, fail, ensure false, mword divide by zero, chr 256). Inputs:
0, ±1, 2^31, 2^32, 2^62, 2^63, 2^64 and neighbours, 2^100/10^30 for
natural/integer, negative operands for div/mod/rem, empty/singleton/
duplicate-laden lists and sets, plus values from an LCG (MMIX constants,
mod 2^64, on `natural`) written in each probe.

Domain restrictions (deliberate, stated in each probe's header): `nat`/`int`
operands and results stay inside [-2^62, 2^62-1] (the ruled 63-bit class);
out-of-range int32/int64 conversions from natural/integer are the ruled D4
class (`f_int32_overflow`); division by zero is the existing `f_*_zero`
probes; inputs on which the OCaml implementation is itself wrong are
excluded and listed as findings below (OM1–OM5, LP1, LP5, LP9).

## 2. Findings

Classification: **FIXED** (LemLib/Lean bug, fixed on this branch);
**OCAML** (ocaml-lib/OCaml-target bug, recorded, semantics not changed —
candidates for an upstream Lem report); **LEM** (lem library definition
bug, identical on both targets); **KNOWN** (already recorded elsewhere);
**QUESTION** (needs an operator ruling).

### LP1 — `defaultMax`/`defaultMin` are structural on OCaml (QUESTION)

`library/basic_classes.lem:260,264`: `declare ocaml target_rep function
defaultMax = \`max\`` / `defaultMin = \`min\`` — OCaml's polymorphic,
STRUCTURAL `max`/`min`. lem's definition is `maxByLessEqual (<=)` (the
`Ord` instance), which Lean follows. `max`/`min` at any type with a
user `Ord` instance (the default `OrdMaxMin` instance) therefore differ
whenever the instance disagrees with structural order. Reproducer
(reversed order):

```lem
type r = R of nat
let r_cmp (R a) (R b) = compare b a
instance (Ord r) let compare = r_cmp  let (<) x y = r_cmp x y = LT
  let (<=) x y = r_cmp x y <> GT  let (>) x y = r_cmp x y = GT
  let (>=) x y = r_cmp x y <> LT end
(* max (R 1) (R 2): OCaml R2, Lean R1;  min: OCaml R1, Lean R2 *)
```

Also Ord-equal but structurally different values (`K 1 "x"`/`K 1 "y"`
under an order on the first field): OCaml `max` returns the second, Lean
the first. The reference rule says OCaml; the OCaml rep contradicts lem's
own definition (and HOL/Isabelle, which use it). [AGENT] recommendation:
treat as an OCaml-target deviation (an upstream report: the rep is only
valid when the instance is structural) and keep Lean on lem's definition;
not registered anywhere (no ruling). `p_lib_misc` exercises only cases
where the two agree.

### LP2 — `declare termination_argument f = automatic` on nat recursion does not build on Lean (QUESTION)

A lem function recursing on `n' + 1` patterns and declared
`termination_argument ... = automatic` is emitted as a plain `def`
(`src/lean_backend.ml`, `auto_term_for`, ~4709), and lem's pattern
compilation gives `lem_if (n == 0) then … else let n' := n - 1; …`. Lean
must prove `h : ¬(n == 0) = true ⊢ n - 1 < n`, but `n == 0` elaborates
through LemLib's `instBEqOfEq0` (`lean-lib/LemLib/Basic_classes.lean:37`,
with the `BEq ↔ Eq0 ↔ SetType` instance chain at :50 and :180), not
`instBEqNat`, so `beq_iff_eq` (which needs `LawfulBEq`) does not apply and
`decreasing_tactic` fails ("failed to prove termination"; with a big
literal in another argument: "maximum recursion depth has been reached").
Reproducer (fails at Lean build):

```lem
let rec f (n : nat) (s : natural) : list natural =
  match n with 0 -> [] | n' + 1 -> s :: f n' (s + 1) end
declare termination_argument f = automatic
```

Fail-noisy (a build error), but a valid lem program the Lean target cannot
compile. A `decreasing_trivial` extension rewriting Bool guards was tried
and does not help (the instance chain hides the Nat equality); a fix needs
either a `LawfulBEq` story for the Eq0-derived instances or an emission
change (dependent `if h :` for guards lem introduced itself). Not fixed
[AGENT]: it is a design change in the instance layer; the probes simply
omit the declare (their LCG helper is a `partial def`).

### LP3 — `natLand`/`natLor`/… ambiguous on Lean (FIXED, `5322853`)

`lean-lib/LemLib.lean` defined root-level `natLand`/`natLor`/`natLxor`/
`natLnot`/`natLsl`/`natLsr`/`natAsr` (for `library/transform.lem`), which
collide with the generated `Lem_Word.natLand`/…: any direct call from a lem
program was `error: Ambiguous term natLor`. Reproducer: `natLor 1 2` in a
probe. Fix: renamed `lemNat*` (now `lean-lib/LemLib.lean:1747`), transform
reps follow. Regression: `p_lib_word_int_nat`.

### LP4 — int/nat bitwise were 31-bit on Lean (FIXED, `5322853`)

`library/word.lem` gives `intLand`/`intLor`/`intLxor`/`intLsl`/`intAsr` and
`natLand`/`natLor`/`natLxor`/`natLsl`/`natAsr` OCaml reps (native 63-bit
`land`/…) but no Lean rep, so Lean ran lem's definitions through a
31-bit `bitSequence` (`bitSeqFromInt = bitSeqFromInteger (Just 31)`).
Verbatim reds (< OCaml, > Lean): `intLsl 1 30: 1073741824` vs `0`;
`intLor 2^30 0: 1073741824` vs `-1073741824`; `natLor 2^40 1:
1099511627777` vs `1`; even `int lsl/asr 5 29 = 2684354560` vs
`536870912`. [AGENT] decision: the Lean reps are UNBOUNDED two's complement
(`lemIntLand`/`lemIntLor`/`lemIntLxor`/`lemIntLsl`/`lemIntAsr` over `Int`,
`lean-lib/LemLib.lean:1764`; `lemNat*` over `Nat`) — equal to OCaml on its
whole domain, and the logical extension where OCaml wraps (the ruled
class). `intFromBitSeq`/`bitSeqFromInt` keep lem's 31-bit definition on
every target. Regression: `p_lib_word_int_nat` (459 lines incl. 2^30..2^62
operands); LemLibTest sign-case examples.

### LP5 — `wordToHex` / `show` on `mword` is a stub on OCaml (QUESTION)

`library/machine_word.lem:1375`: `let {ocaml;isabelle;coq} wordToHex w =
"wordToHex not yet implemented"`; the Lean rep is `BitVec.toHex`. The
`Show (mword 'a)` instance uses it, so `show` of any machine word differs.
Following the reference literally would make Lean print the stub. Not
exercised; [AGENT] recommendation: record as an OCaml-library gap
(upstream), keep Lean's real rendering, or rule it class (c).

### LP6 — mword bit lists were LSB-first on Lean (FIXED, `5322853`)

`mwordFromBitlist`/`mwordToBitlist` treated the list head as bit 0. lem's
own asserts (`machine_word.lem` `wordFromBitlist_test`:
`wordFromBitlist [false;false;true;false] : mword ty4 = wordFromNatural 2`,
`bitlistFromWord_test`), the OCaml reference (`ocaml-lib/lem.ml:162,170`),
HOL `v2w`/`w2v` and Isabelle `of_bl`/`to_bl` are MSB-first. Red:
`bitlistFromWord (w8 2)`: OCaml `00000010`, Lean `01000000`. The existing
suite test only checked the round trip. Fix `lean-lib/LemLib.lean:2016`;
a longer-than-width list keeps its low bits (HOL `v2w`). Regression:
`p_lib_machine_word`, `test_mword.lem` `mw_wordFromBitlist_msb_first`/
`mw_bitlistFromWord_msb_first`, LemLibTest.

### LP7 — `word_extract` ignored `hi` on Lean (FIXED, `5322853`)

`mwordExtract lo _hi w = BitVec.extractLsb' lo result w` (Isabelle
`Word.slice` semantics) returned bits beyond `hi` whenever the result type
is wider than `hi-lo+1`: `word_extract 0 3 (0xAB : mword ty8) : mword ty8`
gave 171; the OCaml reference (`lem.ml:138`) and HOL (`word_extract hi lo`
then `w2w`) give 11. Fix: `(extractLsb' lo (hi+1-lo) w).setWidth result`
(`lean-lib/LemLib.lean:1981`). Regression: `p_lib_machine_word` (value
row), `test_mword.lem` `mw_word_extract_masks_hi`, LemLibTest.

### LP8 — `chr` succeeded above 255 on Lean (FIXED, `5322853`)

`declare lean target_rep function chr = \`Char.ofNat\``: `chr 256` was
U+0100 (`ord` of it 256) where OCaml `Char.chr` raises `Invalid_argument
"Char.chr"` — Lean succeeded where the reference fails. Fix: `lemChr`
(`lean-lib/LemLib.lean:1911`) fails loudly outside 0..255 (0..255 as
before; bytes ≥ 128 as Unicode scalars remain the registered F2 arc).
Regression: `f_lib_chr_range`.

### LP9 — `*By` set operations with a comparator other than the members' (QUESTION)

OCaml sets carry their comparator; `Pset.union s1 s2` uses `s1`'s
(`ocaml-lib/pset.ml:313`) and `bigunion c xss = fold union xss (empty c)`
(`:501`) therefore IGNORES `c` for the result unless all member sets are
empty. The LemLib port passes the comparator explicitly
(`lean-lib/LemLib.lean:806`, `setBigunionBy` :897) and uses `c`.
Reproducer: `Set.size (Set.bigunionBy m3 {{1};{4}})` with `m3 x y =
compare (x mod 3) (y mod 3)`: OCaml 2, Lean 1; `Set_extra.toList
(Set.bigunionBy rev {{1;2};{3}})`: OCaml `[1; 2; 3]`, Lean `[3; 1; 2]` (the
Lean tree merges sets built under another comparator and loses its search
invariant). Related, identical on both targets (so no parity diff, but
ill-formed): `Set.bigunionMapBy rev` / `Set.mapBy`-style operations whose
comparator differs from the argument sets' give unordered trees (e.g.
`[12; 11; 13; 3; 2; 1]` in `p_lib_set_map`). [AGENT] view: using a `*By`
comparator that disagrees with the members' `SetType` is outside what the
Pset port can mirror without carrying comparators in the value; needs a
ruling (mirror OCaml by carrying the comparator, or rule the OCaml
behaviour a representation deviation like the ruled closure-compare
case). `p_lib_set_map` exercises `bigunionBy` only with the members'
comparator.

### OM1 — OCaml `mword` negation not reduced (OCAML)

`ocaml-lib/lem.ml:148` `word_uminus (n,w) = (n, 2^n - w)`: for `w = 0`
the result is the out-of-range 2^n. Consequences, all Lean-correct:
`naturalFromWord (uminus (w8 0)) = 256`, and `uminus (w8 0) = w8 0` is
FALSE on OCaml; `wordFromInteger` (`machine_word.lem:1688`, `uminus` of
`wordFromNatural (-i)`) gives 2^n for every negative multiple of 2^n
(`wordFromInteger (-256) : mword ty8` → 256); `signedDivide`
(`machine_word.lem:1672`) gives 2^n for a zero quotient of opposite-sign
operands (`signedDivide (w8 -1) (w8 5)` → 256).

### OM2 — OCaml `getBit i` reads bits i..2i (OCAML)

`lem.ml:194`: `extract_big_int w i (i+1)` is (offset i, LENGTH i+1), so
`getBit w i` is true if any of bits i..2i is set: `getBit (w8 4) 1` is
true on OCaml (bit 1 of 0b100 is 0; Lean false), `getBit (w8 8) 2` true.
Correct only for i = 0 or when bits i+1..2i are clear.

### OM3 — OCaml `setBit` beyond the width (OCAML)

`lem.ml:187` ORs `1 lsl i` without masking: `setBit (w8 0) 10 true` has
`naturalFromWord` 1024 on OCaml (Lean: unchanged 0, HOL `:+` likewise).

### OM4 — OCaml word size taken from the value, not the type (OCAML)

`wordFromBitlist` (`lem.ml:162`) uses the list length, `word_extract`
(`:138`) `hi-lo+1`, `word_concat` (`:135`) `n1+n2`, whatever the result
type: `wordFromBitlist [t;f;t;t] : mword ty8` has `word_length` 4 and a
4-element `bitlistFromWord`; an 11-element list gives the out-of-range
value 1027 in a `ty8` word (HOL `v2w`/Lean: low 8 bits, 3). Values agree
with Lean whenever the type is consistent with the arguments.

### OM5 — OCaml rotations and arithmetic shifts raise (OCAML)

`lem.ml:226-231`: `word_ror 0` → `Invalid_argument "Z.extract:
nonpositive bit length"`; `rotateLeft n` (= `word_ror 0`) likewise;
`rotateLeft (n+1)` → "Z.extract: negative bit offset"; `rotateRight
(n+1)` and `arithShiftRight` of a negative word by more than the width
(`lem.ml:208`, `ones lsl (n-m)`) → "Z.shift_left: count argument must be
positive". Lean (BitVec) rotates modulo the width and shifts to all-ones.
Note: under the failure-agreement rule these are cases where Lean
SUCCEEDS where the reference FAILS; [AGENT] recommendation: the OCaml
failures are bugs (rotation by 0 is the identity in every prover
backend), so Lean should not mirror them — needs the operator's ruling.

### F1 note — int/int32/int64 `mod` with a negative divisor (KNOWN)

`p_lib_num_nat_int` confirms the mirrored F1 behaviour
(`ocaml-lib/nat_num.ml:12-34`) on large operands: `intMod -7 -2 = -3`,
`intMod -7 -2^61 = -2^61-7` (|remainder| > |divisor|, neither floor nor
Euclidean). Lean mirrors it deliberately (parity-fix record F1); recorded
here as an upstream-report candidate only.

### LU1 — `Set.splitMember` returns its halves swapped (LEM)

`library/set.lem:400`: `splitMember p s = (filter ((<) p) s, p IN s,
filter ((>) p) s)` — `(<) p x` is `p < x`, so the FIRST component holds the
elements ABOVE `p` (`splitMember 3 {1;2;3} = ({}, true, {1;2})`), the
opposite of `split` (`:395`, `(filter ((>) p) s, filter ((<) p) s)`).
Identical on both targets (lem definition). Upstream report candidate.

### LU2 — `defaultLnot` negates instead of complementing (LEM)

`library/word.lem:743`: `defaultLnot fromBitSeq toBitSeq x = fromBitSeq
(bitSeqNegate (toBitSeq x))` — arithmetic negation (`defaultLnot … (-6) =
6`; bitwise complement is 5). No library instance uses it (`integerLnot`/
`intLnot` are `~(i+1)`); identical on both targets. Upstream candidate.

### THE — no OCaml implementation (QUESTION, not probed)

`library/function_extra.lem:38` `declare ocaml target_rep function THE =
\`THE\``: no such OCaml value exists (`p_zz_the`: "There is no constructor
THE within type option" — the OCaml build fails); Lean panics
(`LemLib.lean` `THE`, "Hilbert choice is not computable"). Not realisable
on the reference; counted as uncovered.

## 3. What remains uncovered, and why

- `Num`: the seven `*FromNumeral`/`fromNumeral` take a `numeral`, which a
  lem program cannot name — they are reached by every numeric literal.
  Rational/real/float vals are Lean class (c) refusals (not eligible).
- `Word.bitSeqFromNumeral`, `Machine_word.wordFromNumeral`: likewise via
  literals (`(300 : mword ty8)` is in `p_lib_machine_word`); `size` is a
  class method reached through `size_test_fn`.
- `Machine_word.wordToHex`: LP5. `Function_extra.THE`: no OCaml value.
- Not eligible (one target missing): `Map`/`Set` `*By` variants without an
  OCaml rep (`insertBy`, `memberBy`, `unionBy`, …), `Relation` total
  predicates (`isReflexive`, `relId`, … — HOL/Isabelle only),
  `Debug.print_*` (Lean `LemUnsupported`), `Transform` (not in LIBS).
- Everything else eligible is referenced. Behaviour coverage is per the
  probes' inputs; class-dispatched paths are exercised by the older
  probes and by the named calls here (the same reps).

## 4. Decisions needed

1. LP1 (`max`/`min` structural on OCaml): OCaml deviation or reference?
2. LP2 (`termination_argument automatic` + nat recursion): acceptable as a
   documented limitation, or schedule an instance-layer/emission fix?
3. LP5 (`wordToHex` stub): keep Lean's rendering?
4. LP9 (`*By` with a foreign comparator): mirror OCaml's carried
   comparator, or rule it a representation deviation?
5. OM5 (OCaml rotations/shifts raising): Lean keeps succeeding?
6. Whether OM1–OM5, LU1, LU2, LP1, LP5 and the F1 note go into the upstream
   Lem report bundle.
