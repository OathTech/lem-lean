# Lean backend findings from porting linksem (2026-09-28)

Branch `linksem/fixes` (from `mdd/lean-backend` at `c2a68e7`). linksem
(rems-project/linksem: ELF, DWARF and static-linking semantics in Lem,
~34k lines, 96 model modules) was generated with `lem -lean` and compiled
against LemLib as a second large consumer after Cerberus. Every finding
below was hit by real linksem code; each fix carries a regression test in
`tests/comprehensive` (listed per item).

Provenance: [USER 2026-09-28] charter: "the main purpose of this exercise is
to see whether we shake out any bugs in lem-lean"; fixes and designs below
are [AGENT] unless marked.

Toolchain: Lean 4.28.0 (the `lean-lib/lean-toolchain` pin). Cerberus builds
on 4.32.2; B9 is toolchain-dependent (see there).

## B1. Constants with symbolic names (fixed)

linksem's `error.lem` defines `let (>>=) x f = bind x f` and uses it infix
throughout. The backend emitted `def >>= ...` (a Lean parse error), and
every infix use `x >>= f` resolved to Lean's own `Bind` operator. Even with
`declare {lean} ascii_rep`, only the definition was renamed: Lem's
`ascii_rep_set` holds the constants a definition *defines* (other targets
accept symbolic names at uses), so uses still printed `>>=`.

Fix: a shown constant whose Lean name is not a Lean identifier is rendered
by its ASCII representation at the definition and at every use (prefix
form, operands parenthesised as arguments). Without an ASCII rep the
definition is refused at generation time, naming the fix. The identifier
test is Lean's grammar (`'` allowed), not Lem's `is_simple_ident_string`.
Tests: `test_symbolic_ops.lem` (infix, prefix, chained, application
operands, partial application), `negative/neg_symbolic_def.lem`.

## B2. No `Ord LemOrdering` (fixed, LemLib)

Sets of comparison results (`Set.member (compare a b) {LT; EQ}`, used in
linksem's orderings) need `SetType ordering`, derived from `Ord`. Added
`instance : Ord LemOrdering` with the OCaml target's order LT < EQ < GT
(`ordering` is `int` there: -1 < 0 < 1). Tests: `LemLibTest.lean` (kernel
`decide` pins on `compare`, `Pset.fromList`, `Pset.mem`).

## B3. If/else-if chains deeper than ~128 (fixed)

Lean 4.28 cannot elaborate an else-if chain nested more than ~128 deep
("maximum recursion depth has been reached"), independent of the branch
contents (measured with synthetic chains of 150 and 600 arms; 100 passes).
linksem's AArch64 relocation dispatch has a 123-arm chain inside a larger
term. A `maxRecDepth` bump is not a fix. Chains of more than 96 arms are
emitted in blocks of 64: each later block is a local continuation
`let _lemIfTailN := fun (_ : Unit) => <block>` (innermost first), and a
block's final `else` calls the next. Pure and order-preserving; `zeta`
unfolds it in proofs. Variables of the chain using the reserved
`_lemIfTail` prefix are refused. Test: `test_long_if_chain.lem` (150 arms;
first, middle, both block boundaries, last and fall-through pinned; the
same shape nested in a `let` inside a `match`).

## B4. Nested inductives through type abbreviations (fixed)

linksem's `dwarf.lem` ties a knot through a parameter:
`type c_type_top 't = ... | CT_array of cupdie * 't * list (array_dimension 't)`
and `type c_type = CT of c_type_top c_type`, where `array_dimension` is an
abbreviation. The kernel rejects the nested occurrence ("arg #1 of
'_nested.List_2.cons' contains a non valid occurrence of the datatypes
being declared") because it does not unfold the emitted `abbrev`; the same
definition with the abbreviation written inline is accepted (6-line
repro). In inductive constructor arguments (and mutual-record fields), an
abbreviation without a Lean target rep whose expansion mentions a type
parameter or a type of the group being defined is printed expanded;
closed abbreviations keep their names. Test: `test_nested_abbrev.lem`.

## B5. Incomplete Lean keyword tables (fixed; checker added)

linksem binds `let matches = List.filter ...`; `matches` is a Lean token,
and the output did not parse. Rather than add one word: the new
`scripts/lean_keyword_probe.sh` derives from the pinned toolchain every
identifier-shaped core-grammar token that fails as a binder (166 on 4.28)
and checks that BOTH avoid lists contain it: `lean_syntax_keywords` in
`src/lean_backend.ml` (local names) and `library/lean_constants`
(top-level names). 86 were missing from the first, 82 from the second
(`matches`, `repeat`, `while`, `mut`, `until`, `Type`, `Prop`, `bif`,
`dbg_trace`, ...). Re-run it when the toolchain moves; it fails loudly and
refuses a vacuous (empty) token table. Test: `test_keywords.lem` (B5
section: locals and a top-level `matches`).

## B6. Parenthesised binder parameters (fixed)

`let analysed_locations_at_pc (ev) (ds: dwarf_static) ...` rendered `(ev)`
as `((ev : T))` ("expected '_' or identifier"); likewise `((z))` and `(_)`.
In parameter position, source parentheses around a pattern that already
renders as a parenthesised binder (variable, wildcard, typed pattern,
annotated variable, unit) are dropped. Test: `test_patterns.lem` (B6
section).

## B7. Mutual-record literals emitted in the wrong order (fixed; silent miscompile class)

Records in a mutual block are emitted as single-constructor inductives and
their literals as positional `T.mk v1 v2 ...`. The values were emitted in
the order the LITERAL lists its fields, not the declaration order. linksem's
`sdt_subroutine` literal lists `ss_unspecified_parameters` before
`ss_pc_ranges`: a type error there, but wherever the swapped fields share a
type it compiles and silently exchanges them. Fixed: values are placed by
the type's declared field list, matched by field descriptor; a literal
that does not give every field exactly once is refused. (Record update
already used the declared list.) Test: `test_mutual_record_order.lem` (two
`nat` fields swapped in the literal; every field asserted).

## B8. `fail` and closed-term extraction (fixed)

LemLib's `Lem_Assert_extra.fail {a} [Inhabited a] : a := failwithI "fail"`
is an ordinary definition: every use `@fail Char inst` is a closed term,
which Lean 4.28 hoists into a module initialiser. linksem's
`hex_char_of_nibble` ends in `else fail`, so every program importing
`missing_pervasives` panicked at START-UP. Panic messages are disabled
during initialisation, so the symptom under `LEAN_ABORT_ON_PANIC=1` was a
silent SIGABRT (exit 134, no output); without it, the run looked normal.
Localised with one probe executable per module (`import M; def main :=
pure ()`) and the generated C of the initialiser. Fix: a polymorphic
definition with no explicit parameters and a non-function type is emitted
`@[never_extract]` (as `failwithI` itself is). Test:
`test_untaken_failure.lem` / `lean-untaken-failure` (`pick_char`).

## B9. Closed calls in untaken branches evaluated at load (fixed; toolchain-dependent)

B8 is one case of a general hazard: on Lean 4.28 ANY closed application of
a partial function, anywhere in a function body, is hoisted and evaluated
when the module loads. Probe: `def f (b : Bool) := if b then g 10 else 0`
with `g 10` a `failwithI` aborts at start-up although the branch is never
taken; the OCaml target evaluates it only when reached. The existing
`TestFailwithThreadingPanic.lean` comment records the same effect in
LemLib's own modules as a "toolchain caveat (4.28)" and notes that on
≥ 4.32 closed terms are initialised lazily. Fix: generated modules are
compiled with `set_option compiler.extract_closed false` (emitted after the
imports): strict, in-place evaluation, as in OCaml, on every toolchain.
Top-level constants are unaffected (initialised at load on both targets).
Cost: closed subterms are recomputed per evaluation instead of cached;
measured on linksem in the record's timing section. Test:
`lean-untaken-failure` (leg 1: untaken branches, exit 0 under
`LEAN_ABORT_ON_PANIC=1`; leg 2: the taken branch fail-stops with its
message).

## B10. Reserved-name lists loaded fail-open (fixed; upstream Lem)

`Initial_env.read_target_constants` wrapped the load of
`library/<target>_constants` in `try ... with _ -> NameSet.empty`: any failure
to read the file silently disabled the renaming pass for that target. For
Lean that means unescaped keywords (`from`, `by`), constructors ambiguous
with the root namespace (`One`, `Add`, `Seq`) and class names colliding with
Lean's (`Ord`): broken output, no diagnostic. It happened for real (B12):
seven parity probes failed to compile in one suite run with exactly those
errors. Targets that ship a constants file (ocaml, hol, isabelle, coq, lean)
now fail loudly if it is missing or unreadable; tex/html/lem (no file by
design) keep the empty set. Output is unchanged whenever the file reads.
Test: `lean-constants-required` (plant: a library copy without
`lean_constants` is refused; the intact library generates).

## B11. Local lambda lets with destructuring parameters (fixed)

linksem's `link.lem` binds `let apply_reloc = fun img -> fun (el_name, start,
len) -> fun s -> fun a -> ...`. Lem's pattern compiler makes the tuple
parameter a `match p with | (el_name, start, len) => fun ...`; with no
expected type Lean infers a DEPENDENT motive, and the local function gets a
type like `?m img p` that cannot be applied ("Function expected"). A local
`let x = fun ...` without an annotation is now annotated with the
right-hand side's Lem type. Test: `test_lambda_let.lem` (monomorphic, and
inside a polymorphic definition).

## B12. Relative `LEMLIB` exported by the suite Makefile (fixed; harness)

`tests/comprehensive/Makefile` set `LEMLIB = ../../library`. If `LEMLIB` is
set in the caller's environment (lem's own docs suggest it), make exports
the Makefile's value to every recipe, and the relative path is wrong for
recipes that change directory (`parity/run.sh`): before B10 the parity
probes then silently compiled with no reserved-name list; after B10 the
admission test failed loudly. Now `$(abspath ../../library)`.

## Open

- **L1** `Link.lean` (linksem's linker, outside the `main_elf` cone):
  `if binding_is_final options b then ...` fails with "Application type
  mismatch ... Bool ... expected Prop" (`Decidable (... = true)` reported
  "stuck" with no visible metavariables). Established by bisection on the
  generated file:
  - emitting the local `let binding_is_final : T := v` as `have` fixes it;
  - replacing `v` by a trivial function fixes it;
  - `v` containing ANY nested `match` on its `Option` component (even with
    constant arms) triggers it;
  - ascribing either `match`'s type, or the operands, does not help;
  - `bif` in place of `if` compiles;
  - standalone reconstructions of the same shape (including inside a
    `List.foldl` lambda and with type abbreviations) do NOT reproduce it.
  So instance synthesis for the `if` sees a let-variable whose value still
  has a pending elaboration problem, in a context-dependent way. Candidate
  backend fixes, each with broad output impact (hence not taken without an
  operator decision): render Lem's Bool `if` as `bif`/`cond` (no Decidable
  search at all; changes every conditional and ite-based proof style), or
  emit non-dependent local lets as `have`.

## Impact on the Cerberus tree (measured, not re-pinned)

The Cerberus Lean tree (`LEM_SRC_LEAN`, 85 sources, 170 files) generated
into scratch directories with pristine c2a68e7 and with this branch, same
flags as `make lean-prelude-src`; the cerberus checkout was not touched.
Differences, all in the categories above:
- B9: `set_option compiler.extract_closed false` in all 170 files;
- B8: 9 `@[never_extract]` (nullary polymorphic definitions, e.g. `empty_sigma`);
- B11: ~120 local lambda lets gain a type annotation;
- B4: a few constructor arguments print an abbreviation expanded
  (`continuation_element`'s `Kunseq`/`Kwseq`/`Ksseq`).
No `.mk` literal changes (B7 does not affect Cerberus: no mutual-record
literal lists its fields out of declaration order), no B3 chunking, no
renames. Before any re-pin: measure the B9 performance effect on the
Cerberus lanes (closed subterms are recomputed rather than cached; Cerberus
runs on 4.32, whose lazy closed-term initialisation already avoids the
load-time evaluation B9 addresses, so B9 buys it semantics-independence
from the toolchain at a possible runtime cost). Operator decision.
