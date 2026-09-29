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

## B13. Lem `if` emitted as Lean `if` got stuck in context (fixed; was L1)

linksem's `link.lem` (`mark_fate_of_relocs`) failed with "Application type
mismatch: `binding_is_final options b` has type Bool but is expected to have
type Prop in `@ite ...`". Root cause, from a `trace.Meta.synthInstance` run
on a delta-debugged reduction (12k -> 2k characters, every step re-checked
for the same error): Lean's `if c then t else e` expands to `let_mvar% ?m :=
c; wait_if_type_mvar% ?m; ite ?m t e`; for a Bool `c` the elaborator must
solve the coercion problem `CoeT Bool c Prop` (whose goal CONTAINS the term
`c`) and then `Decidable ?m`. Here `c` mentioned a let-variable whose value
still carried a postponed `match`, the coercion problem failed with an
internal stuck exception, `Decidable ?m` stayed unsolved, and `ite` was typed
with the uncoerced Bool. Standalone reproduction (plain Lean, no Lem): a
`List.foldl` lambda with tuple matches, a let-bound typed lambda whose body
matches on an `Option`, a value from a polymorphic helper with instance
arguments, a destructuring `match` on it, then `if f x b then ...`.

Every Lem `if` has a `bool` condition, so the backend now emits LemLib's
`lem_if c then t else e`, which expands to `@ite _ (c = true)
(instDecidableEqBool _ _) t e`: no coercion and no instance search (the
instance's arguments are solved by unification), the condition written
once, and the SAME kernel term Lean elaborates for a Bool `if` (checked on
the elaborated definitions in `LemLibTest`, plant-tested with a `cond`
expansion), so proofs over generated code are unaffected. Caveat, stated
exactly: the identity holds when the RENDERED condition is a Bool, which it
is for every live conditional in LemLib, linksem and the tests (checked: the
only Prop-rendered conditions are in commented-out bodies of definitions
with target reps); a condition whose Lean target rep produced a Prop would
elaborate as `decide p = true`: same behaviour, not the same term. Prop contexts
(indreln premises, `St.prop_equality`) keep the builtin `if`. `lem_if` is a
token, reserved in both avoid lists. With it the whole linksem model
compiles, `Link.lean` included (214 jobs). Test: `test_if_bool_cond.lem`
(the linksem shape in Lem; plant: pristine c2a68e7 output fails to compile
with the original error, this branch compiles and its assert passes).

## B14. Instances at several tuple arities resolved by Lean, not Lem (fixed)

Found by the `main_link` lane (2026-09-29). Lem tuples are n-ary; Lean's
are right-nested pairs, so the Lean type of a Lem triple whose LAST
component is a pair, `a × b × (c × d)`, IS the Lean type of a quadruple.
A class with instances at several tuple arities (linksem's `Show`: pair,
triple, quad) therefore has overlapping Lean instances at such a type, and
Lean picks the most recently declared one: `(1, 2, (3, 4))` showed as
`(1, 2, 3, 4)`, a pair `(1, (2, 3))` as a triple. Lem inlines a method at a
known instance (so the top-level choice was right in generated code); the
wrong choice was in the instance ARGUMENTS Lean re-resolves (a list of such
triples, a generic caller, a nested pair) and in hand-written Lean calling
the class method (linksem's `main_link` driver, since fixed to call what
Lem resolves to). Fix: non-default tuple instances get a global name
(`lemInst_[Lem_]<module>_Instance_<class>_<type>`, `Lem_` for library
modules, since linksem's `Show` and LemLib's `Show` both have a pair
instance); a use of a constant whose class constraints reach a confusable
tuple type (Lem's own resolution, `get_matching_instance`) binds exactly
Lem's instances locally, innermost first (`haveI := lemInst_... (a := T1)
...; e`); Lean's local instances take precedence over global ones.
Exempt: Basic_classes' `Eq`/`Ord`/`SetType`/`MapKeyType` (their tuple
instances are componentwise / lexicographic, so the overlap computes the
same result). The supply-threaded paths refuse such a use (loud). Test:
`test_tuple_inst_arity.lem` (7 asserts; with the bindings stripped, 3
fail: nested, list, generic). LemLib: one instance renamed
(`Lem_Show` pair). linksem: instance names only (no confusable use in the
model).

## B15. `let _ = e1 in e2` dropped e1 (fixed)

Found by the `main_link` lane (a model diagnostic missing on stderr). Lem's
sequencing idiom evaluates e1 for its effect; OCaml is strict, so e1 runs
and a failure in e1 stops the program. Lean's compiler drops an unused pure
`let`, and treats any `Unit` value as `()` (even `match e1 with | () => e2`
and an opaque `implemented_by` consumer of the value were removed): the
model's `errln` diagnostics vanished and, worse, a FAILING e1 was skipped
(fail-open). Fix: `let _ = e1 in e2`, `let () = e1 in e2` (which reaches
the backend as a one-arm match) and one-arm matches on `_`/`()` are emitted
as `lemSeq (fun _ => e1) (fun _ => e2)`. LemLib's `lemSeq` is logically
`e2` (`b ()`); its `implemented_by` body forces e1 by storing the value in
a fresh `IO.Ref` (a `BaseIO` effect the compiler keeps; a pure "use",
`if ptrAddrUnsafe x == 1 then b () else b ()`, was simplified away and
arity reduction then dropped the argument). A variable or literal e1 keeps
the plain emission (no effect possible). The supply-threaded paths refuse
a pure e1 (loud). Inside the discarded e1 no expected type flows in, so an
empty list literal of a closed Lem type is ascribed (`([] : List domain)`):
Cerberus's hand-written `print_debug_pure : Nat → List d → ...` is more
general than Lem's `list domain`, and `lemSeq (fun _ => print_debug_pure 2
[] ...)` otherwise leaves `d` unsolved. (The old `match e1 with | () =>
e2` elaborated only because Lean discards the discriminant of a `()`
pattern: e1 was dropped already in the elaborated term.) Tests: parity
failure probes `f_let_seq.lem`, `f_let_unit.lem` (OCaml and Lean both fail
with the discarded e1's message; pre-fix the Lean binary printed the next
step and exited 0).

Cerberus impact of B15: 266 sites (its `print_debug_pure`/`warn` debug
calls, no-ops in its Lean twins, so no behaviour change). Two hand-written
proofs unfold definitions through these sites and need `lemSeq` in their
`simp only` sets (`Core_run_aux_lemMeasureProofs.lean`,
`Driver_lemMeasureProofs.lean`: one word each; verified in the scratch
clone, 395 jobs build). This is an edit for the Cerberus re-pin, not made
in the Cerberus checkout.

Cerberus behaviour with A1 + B14 + B15 (scratch clone, csmith corpus lane,
`scripts/measure_csmith_cpu.py --max 200`): 97 match, 102 CERB_SKIP, 1
timeout, 0 baseline regressions after A1 and again after B14/B15 (the same
statuses as before A1). Lean CPU over the 97 matched inputs: 34.82 s (A1),
32.58 s (B14/B15); the unchanged OCaml oracle moved by the same order
(14.34 s, 13.17 s), so no measurable cost.

## Impact on the Cerberus tree (measured, not re-pinned)

Generated with this branch (lem `65389aa`) in a scratch clone of cerberus-lean
`d62f52121` (the container checkout untouched): 170 files; differences from
c2a68e7 output are B4 expansions, B8 attributes (9), B9's option (170 files),
B11 annotations (~120) and B13 `lem_if` (414). No `.mk` literal reorderings
(B7 does not affect Cerberus). The tree COMPILES (395 jobs, Lean 4.32.2,
LemLib from this branch by path).

B9 cost, A/B on that one tree (only difference: the `set_option` lines in
the 170 modules and LemLib's generated modules), csmith corpus lane via
`scripts/measure_csmith_cpu.py --max 200` (CPU = user+sys, GNU time):
- Lean CPU over the 97 inputs Lean ran and matched in both: A (extraction
  on) 32.61 s, B (B9) 39.45 s: +21.0 %; per input over the 10 inputs with
  >= 0.5 s: median +12.6 %, range +2.3 % .. +73.2 % (sa_csmith_272:
  5.38 s -> 9.32 s); max RSS +4.2 %.
- control, the unchanged OCaml oracle binary: B/A = 0.992 (the load moved
  between 3.7 and 58 across the runs; CPU is comparable to ~1 %).
- lane statuses identical in both variants.

Toolchain check of the hazard B9 removes (`if b then g 10 else 0`, `g 10`
panicking, run with `LEAN_ABORT_ON_PANIC=1` and no arguments): Lean 4.28.0
aborts at start-up (exit 134); Lean 4.32.2 exits 0 (closed terms are
initialised lazily at first use), and still aborts when the branch is taken.
So B9 is required on LemLib's pinned 4.28.0 and buys nothing on 4.32.2,
where it costs ~21 % CPU on this lane. Options (operator decision): keep B9
unconditional; or move lem-lean's toolchain pin to 4.32.2 (Cerberus's) and
drop the option, keeping `lean-untaken-failure` as the guard that fails if a
toolchain with eager closed-term initialisation comes back.

## Toolchain move to Lean 4.32.2; B9 retired (2026-09-29)

[USER 2026-09-29] agreed: move lem-lean's pin to Lean 4.32.2 (Cerberus's
toolchain; on the roadmap) and drop B9. All five `lean-toolchain` files now
pin 4.32.2; generated modules no longer set `compiler.extract_closed false`
(the backend comment at the former emission site records why); B8
(`never_extract` on nullary polymorphic definitions) stays; the
`lean-untaken-failure` target is now the guard of lazy closed-term
initialisation and passes on 4.32.2 without the option. The keyword probe
found 12 identifier-shaped core tokens new in 4.32.2 (`cbv_eval`,
`cbv_simproc`, `idbg`, `inferInstanceAs`, `unlock_limits`, ...); they were
added to both avoid lists.

## Audit follow-up (2026-09-29)

Five independent auditors compared the Lean port of linksem with the OCaml
build; the linksem record lists every item. Backend-side:

- **A2. Panics continued by default (fixed).** A reached `failwithI` is a
  Lean `panic!`, which prints and CONTINUES with the `Inhabited` default
  unless `LEAN_ABORT_ON_PANIC=1` is set; an executable over generated code
  could then exit 0 with plausible output where the OCaml target raises
  (linksem: invalid program-header flags printed a table with an empty
  column). LemLib now provides `lemFailStop : BaseIO Unit` (the runtime's
  `lean_internal_set_exit_on_panic`, as Lean's own shell uses; no `import
  Lean`), to be called first in `main`: a reached failure then prints its
  message and exits 1. Test: `lean-untaken-failure` leg 3 (without the
  environment variable; plant: removing the call makes it fail).
- **A3. Failures inside function-returning definitions fire later (documented
  limitation).** Lean's compiler eta-expands every definition to the arity of
  its TYPE (`Lean/Compiler/LCNF/ToDecl.lean:155`, `Meta.etaExpand`, no
  opt-out short of `@[extern]`/`@[init]`), so for `f (x) : A -> B := if c
  then g else failwith ..` the body runs when the returned function is
  applied, whereas OCaml runs it when `f` is applied to `x`. Only the timing
  of failures (and non-termination) differs; the outcome flips only if a
  failing function value is built and never applied. linksem reaches it with
  an unknown DWARF attribute form (both sides fail, different messages).
  Matching OCaml would need a non-function wrapper type for every such
  definition and its uses; not taken.
- **A4. Failure order (documented limitation, existing).** OCaml evaluates
  arguments right to left, Lean left to right: with two failing
  subexpressions the reported failure differs (both fail).
- **A1. Comparison residuals (confirmed, fixed).** Lem's default `Eq` /
  `SetType` / `MapKeyType` instances are OCaml's polymorphic compare, valid
  at every type. The backend's comparisons at a type with a type variable
  that carried no Lem constraint resolved to priority-50 fallback instances
  whose methods panicked (~200 sites in linksem). Because of A2 the
  panic returned a default value: sets kept duplicates (`tag_image` twice:
  OCaml 2 tags, Lean 3), and the Lean linker built an executable with entry
  point 0 and no `.text`. Types with function-typed fields
  (`amd64_abi_feature`) panicked on EVERY comparison, not only when a
  closure is reached. Fix (design:
  `doc/notes/2026-09-29_comparison-dictionaries-design.md`): Lem-instance-guided
  threading of `[Ord a]`/`[BEq a]` binders (transitive, fixpoint);
  function-typed positions are compared structurally with
  `lemFunctionalCompare`/`lemFunctionalBeq`, which fail like OCaml's
  `compare: functional value`. The fallback instances are DELETED, so any
  missed demand is a compile error. Tests: `test_cmp_threading.lem` (the
  pristine output fails 3 of 4 asserts), `test_fn_field_compare.lem`.
  linksem: no fallback left; one loud residual remains
  (`allocated_sections_map`, a map over a mutual sibling, never compared).
  Cerberus (scratch clone `d62f52121`, container checkout untouched): 23
  generated files change (729 fallback-instance lines deleted, threaded
  binders, derived comparisons for function-field types such as
  `pre_execution`); the tree compiles (395 jobs) against this LemLib.
