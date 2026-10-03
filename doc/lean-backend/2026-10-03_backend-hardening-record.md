# Backend hardening, package A: correctness and fail-closed (2026-10-03)

Branch `arc/backend-hardening` from mainline `mdd/lean-backend` at
`5dfcd25`. This record covers package A of the arc that acts on two
reports of 2026-10-03 against `5dfcd25`: the read-the-code review of the
backend and LemLib (the "code review": items H1, H2, M1, M2, W8, TODO 37)
and the behavioural noodler (the "noodle report": findings 1–6). Package C
(cleanup, no output change) is a later slice; package D is out of scope.

## Rulings (verbatim, operator, 2026-10-03)

- Packages: "A: correctness + fail-closed (Recommended)" and "C: cleanup,
  no output change (Recommended)". C is a later slice; D is not in scope.
- #1 min/max: "Register as deviation".
- #2 the BEq bridge: "Design pass first". Another agent handles it; LemLib's
  instance priorities are not changed here.

Every decision below that is not one of these is [AGENT].

## Method

Each item was reproduced first on `5dfcd25` (the worktree before any
change), then fixed, then given a `tests/comprehensive` test that fails on
the before-fix binary and passes after (§"Plants"). The before-fix binary
is a scratch build of `git archive 5dfcd25`. Lean is 4.32.2; every Lean
invocation ran through `cerberus-lean/scripts/capped`. The consumer inputs
were frozen: Cerberus at `51a7402ce`, linksem at `f54d119`.

## Items

### 1. (#4) The Lean annotation words as `target_rep` parameter names — FIXED

- Reproducer: ``declare ocaml target_rep function foo fuel = `Stdlib.succ` fuel``
  → `File "pk.lem", line 4, character 38: Syntax error`; the same line with
  `x` is accepted; upstream Lem accepts `fuel`.
- Cause: `src/parser.mly` `x_ls : | X x_ls` consumed the raw `X` token, while
  the lexer tokenizes the thirteen annotation words for every target; only
  the `x` nonterminal turned them back into identifiers.
- Fix (shared code): a nonterminal `x_tok` (the `X` token or any of the
  thirteen word tokens, yielding the same `(skips, text)` pair) used by both
  `x` and `x_ls`; `loc ()` spans are unchanged. `ocamlyacc -v`: 2
  shift/reduce, 2 reduce/reduce, 5 rules never reduced — identical to the
  fork before the change and to upstream.
- Non-Lean output: `make nonlean-regress` byte-identical; the drift check
  below. The change accepts programs the fork rejected; it rejects nothing
  it accepted.
- Test: `test_contextual_keywords.lem` — an OCaml `target_rep` with
  parameter `fuel` and a Lean one with parameters `reader supply`, both
  applied and asserted.

### 2. (#5) Record fields named like Lean keywords or structure-generated names — FIXED (escape) / REFUSED (generated names)

- Reproducer: `type r = <| at : nat; other : nat |>` → `structure r where\n  at : Nat`
  (Lean: `unexpected token 'at'`), while the literal `{ «at» := default, … }`
  was escaped; `mk : nat` → `Invalid field name mk: This is the name of the
  structure constructor`; `casesOn` → `(kernel) constant has already been
  declared 'r.casesOn'`.
- Measured (plain Lean 4.32.2, a structure, a recursive structure and the
  single-constructor inductive with accessors — the three shapes the
  backend emits): `mk rec recOn casesOn noConfusion noConfusionType` fail in
  all three; `below brecOn` fail for the recursive structure only;
  `binductionOn ibelow induct sizeOf injEq inj toString default ext ext_iff
  mk_inj sizeOf_spec` are fine.
- Decision [AGENT]: keywords are ESCAPED at every site, so a field keeps
  its name (DESIGN: fields keep their Lem names); the eight generated names
  are REFUSED at generation, naming the field and the Lean declaration —
  escaping cannot help («rec» is rec), the reserved-name pass does not
  rename fields (DESIGN "Reserved-name avoidance"), and a rename would be a
  consumer-visible API change applied across six emission sites.
  `below`/`brecOn` are refused for every record (TODO item 47 notes the
  over-refusal for non-recursive ones).
- Fix: `field_ident_to_output` (projection, literal, update, field update)
  escapes; the new `field_decl_output` is the declaration side at the
  three sites (structure field, mutual-structure field, indexed
  single-constructor field); the accessor defs of a mutual record and the
  positional update escape too; `lean_check_type_block` refuses the
  generated names.
- Tests: `test_records.lem` (thirteen keyword fields: projection, literal,
  update, pattern, equality), `test_mutual_record_order.lem` (keyword
  fields of a mutual record, through the accessors),
  `negative/neg_record_field_mk.lem`, `neg_record_field_casesOn.lem`
  (the inductive form).
- Consumers: neither Cerberus nor linksem has a field in either class
  (grep of the frozen sources); their trees are byte-identical.

### 3. (#6) A type variable named like a type or value in scope — FIXED (values) / REFUSED (type definitions)

- Reproducer: `type t = A | B` with `let f (x : 't) (y : t) : nat = tn y`
  → `def f { t : Type } (x : t) (y : t)` (`y` has type `t` but is expected
  to have type `_root_.t`); `let a : nat = 3` with `let f (x : 'a) : nat = a`
  → `a` has type `Type`.
- Fix: `lean_tyvar_renames_for` collects every name the definition refers
  to — the Lean name of each constant (`exp_constants`), the Lean name and
  the components of a Lean target representation of each type constructor
  in the type of any sub-expression or pattern (`lean_types_of_exp`,
  `lean_types_of_pat`, `lean_type_path_names`) — and a type variable equal
  to one of them is rendered under a fresh PRIMED name (`t'`, `t''`, …) that
  is none of those names, none of the other type variables, none of the
  definition's binders (`exp_bound_names`, `pat_to_bound_names`) and not
  reserved. The map is [render]-scoped (`St.tyvar_renames`, set in
  `val_def`, restored by `Fun.protect`) and consulted by the implicit
  binders, both source-type renderers, the class-constraint binders and the
  comparison-dictionary binders.
  - Why primed: a digit-suffixed candidate met Lem's own renamer, which
    turns a colliding LOCAL binder into `t1` at render time, after the map
    is computed (first attempt: `let t = tn y` became `t1` and so did the
    type variable; the Lean error was `List t1` applied to a `Nat`). Lem's
    renamer (`default_avoid_f`, `Name.fresh`) never produces a prime.
  - Type DEFINITIONS are refused, not renamed [AGENT]: a type parameter's
    name is part of the generated API (`inductive t (a : Type)`, named
    arguments), and the collision is a rare source condition; numeric type
    variables are not renamed (no collision shape known). TODO item 47.
- Tests: `test_tyvar_collision.lem` (type and value collisions, a binder
  named like the first candidate, a nested annotation plus a local named
  like the type), `negative/neg_tyvar_type_param_collision.lem`.
- Consumers: byte-identical trees, so no definition of either mentions a
  name equal to one of its type variables.

### 4. (#8) Mutual-record update does not parenthesise or bind its base — FIXED

- Reproducer (heterogeneous block, `skip_instances`): `<| mkr n with f = 5 |>`
  → `(r.mk 5 (mkr n.g))`, which Lean reads as `mkr (n.g)`; a conditional
  base likewise; and the base was re-rendered per unchanged field.
- Fix: `(let lemRecBase := mkr n; r.mk 5 lemRecBase.g)` — the base is
  bound once. `lemRecBase` joins `lean_reserved_exact_names`; a free
  variable of that name in the base or an updated value, or a constant
  rendering to it (`lean_reserved_capture_check`), is refused.
- Tests: `test_mutual_record_order.lem` (an application base, a
  conditional base), `negative/neg_recup_reserved_base.lem`.

### 5. (#9) Generation exponential in wide wildcard patterns — FIXED

- Reproducer (`lem -lean`, a constructor pattern of N−1 wildcards): N=45
  1.6 s, N=47 >120 s, N=50 >120 s; `-ocaml`, `-coq`, `-hol`, `-isa` on N=47:
  1.4–1.7 s. So the cost was in the Lean pipeline after pattern compilation
  (the Coq pipeline shares `is_coq_exp`/`check_match_exp`).
- Cause (stack sample via a temporary `Sys.catch_break` and `-debug`):
  `Lean_layout.be`/`fits` nested dozens deep. The Wadler/Leijen printer's
  `be` decided a Break-mode group by `fits` over a `Seq.t` candidate, then
  re-ran the same `be` to emit it; OCaml's `Seq` is call-by-name, so every
  consumer recomputed the candidate's tail, and each recomputation
  re-decided every Break-mode group that followed on the line — exponential
  in the number of sibling groups on a line that overflows the width. The
  cliff at 46→47 is where `| C _ _ … z =>` stops fitting in 100 columns.
- Fix (`src/lean_layout.ml`): `Seq.memoize` on the candidate of `Group` and
  `Union` — the call-by-need sharing Wadler's complexity argument assumes.
  The decisions are the same, so the output is unchanged (consumer trees
  byte-identical). After: N=47/50/55 1.7 s, N=150 1.6 s, the noodler's
  `t_tuple60` 1.6 s, `t_ctor60_vars` 1.4 s (was 17.6 s).
- Test: `test_wide_patterns.lem` (a 120-field constructor — under the item 6
  limit — with first/last patterns, 60-tuples), compiled and asserted; the
  suite phase `lean-wide-patterns` generates it under `timeout 60` first in
  the suite (`LEAN_WIDE_PATTERNS_SECONDS`), so a regression fails loudly
  instead of hanging the later phases.

### 6. (#3) Records with 128 or more fields segfault at run time — REFUSED at generation

- Confirmed in plain Lean 4.32.2 (no LemLib), binaries run with arguments
  so nothing folds: a 128-field structure of `Nat` exits 139, 127 prints;
  a 128-argument constructor exits 139; 127 `Nat` fields plus one `Bool`
  (1025 bytes) exits 139; 128 and 200 `Bool` fields (one byte each) print.
  So the limit is the object size: header plus pointer-sized fields past
  the runtime allocator's 1024-byte small-object limit. No sound workaround
  that keeps the record's semantics exists at the backend level.
- Fix: `lean_check_constructor_width` refuses a record or constructor with
  more than `lean_max_constructor_fields = 127` fields, counting every field
  at the pointer size (the upper bound), with a message naming the count,
  the limit, the crash and the remedy. Conservative by construction: it
  admits exactly the widths that cannot reach the limit and over-refuses a
  wide record of one-byte fields, loudly. The check runs from `def`'s
  `Type_def` arm (`lean_check_type_block`) so single records, which `def`
  dispatches straight to `type_def_record`, are covered (the first version
  sat in `type_def` and missed them; caught by the reproducer).
- Not a magic value: it mirrors a limit of the Lean runtime, not a choice
  about the semantics; the OCaml target is untouched.
- Tests: `negative/neg_record_width_128.lem`, `neg_variant_width_128.lem`;
  the 120-field constructor of `test_wide_patterns.lem` is the positive
  side.

### 7. (#7) `termination_argument … = automatic` on an `n - 1` recursion — NOT FIXED; DESIGN corrected

- Reproducer: `let rec cnt n = if n = 0 then 0 else 1 + cnt (n - 1)` with
  the declare → `def cnt (n : Nat) : Nat := lem_if n == 0 then 0 else 1 + cnt (n - 1)`
  → `fail to show termination … h✝ : ¬(n == 0) = true ⊢ n - 1 < n`.
- Measured, plain Lean 4.32.2: `if n = 0` (Prop) passes; `if (n == 0) = true`
  with core's `BEq` fails by default and passes with
  `decreasing_by all_goals simp_all; omega` (also `if h : …` + `simp at h;
  omega`). With LemLib imported the condition is
  `@BEq.beq Nat (@Lem_Basic_classes.instBEqOfEq0 Nat Lem_Num.instEq0Nat_1) n 0`
  (`#synth BEq Nat` → the bridge), and `simp_all`, `simp at h` and `omega`
  all fail: "No usable constraints found".
- Decision [AGENT]: no clean general fix exists on this side of the `BEq`
  bridge design pass (#2, "Design pass first", another agent). A
  `decreasing_by` script would have to unfold the bridge's instance chain
  per base type — a special path for one shape, tied to an instance design
  under revision. A generation-time refusal is not possible either (the
  backend cannot know which recursions Lean's checker will accept) and would
  break the consumers: Cerberus declares `automatic` on four structural
  list recursions (`utils.lem`), linksem on `unzip3`. The failure is a loud
  Lean build error, so nothing is silent. DESIGN's row and the manual no
  longer promise "total either way"; they state the limit, the measured
  cause and the remedy (`fuel`/`fuel_measure`/`structural`). TODO item 45
  carries the fix, sequenced after the bridge pass.

### 8. Fail-open spots from the code review — FIXED

- `type_def_indexed` `| _ ->` emitted an empty `inductive … Type 1 where`:
  now raises (`Te_abbrev` reaching it is an internal error, as in `tyexp`;
  `Te_opaque` was already matched earlier).
- `P_num_add` rendered `(name + k)` "invalid Lean but visible": now raises
  unless `St.rendering_comment` (library text behind a representation).
- `lean_cmp_prepass` `depth > 50 → default_all ()` silently
  over-approximated comparison binders (which changes a declaration's
  type): now the same loud refusal as its twin in
  `lean_tuple_inst_demands`.
- The W8 non-exhaustive match in the derived-size builder (`CSfn`
  missing): `CSbad | CSfn` now raise an internal error (`lean_size_shape`
  produces neither); the fork's only default-flag warning in
  `lean_backend.ml` is gone.
- `process_file.ml` ignored `Sys.command "mkdir -p"`: replaced by
  `Sys.mkdir` with parents, a failure a fatal error naming the directory.
  Test: suite phase `lean-outdir-refusal` (`-outdir Makefile/sub`, whose
  parent is a file). TODO item 37 closed.
- No test reaches the three internal-error raises (the inputs do not exist
  after pattern compilation / type-def dispatch / the size shape
  analysis); they are recorded here.

### 9. State fixes — DONE

- `lean_cmp_bounds` moved into `St` ([invocation] lifetime, like
  `reader_lifted`), reset by `reset_invocation`; `if_tail_counter`
  ([invocation]) and `current_type_block` ([file]) reset too, and the new
  `tyvar_renames` ([render]).
- `lean_analysis_prepass_all` now runs `lean_cmp_prepass`, in the order
  `lean_defs` uses, so a module typechecked but not emitted in an
  invocation contributes its comparison-binder demands.
- `reset_invocation` still has no caller (TODO item 6 is the threading
  work); unchanged.

### 10. (#1) `min`/`max` under a user `Ord` instance — REGISTERED as a ruled deviation

- Reproducer (noodle `p_user_ord_instance`): `min (T 1 0) (T 2 0)` is
  `(1, 0)` on OCaml and `(2, 0)` on Lean; everything else about the
  instance agrees.
- Cause: `library/basic_classes.lem` `defaultMax = maxByLessEqual (<=)`
  with ``declare ocaml target_rep function defaultMax = `max` `` (Stdlib's
  structural `max`); upstream report `doc/upstream-tray/11-default-max-min-structural-on-ocaml.md`.
- Ruling: [USER 2026-10-03] "Register as deviation". No OCaml
  representation is changed.
- Register: `parity/probes/p_user_ord_minmax.lem` (the instance's `<=`,
  `min`/`max` both ways, and the explicit `maxByLessEqual (<=)` /
  `minByLessEqual (<=)` lines that agree); `expected_failures.txt` class
  `ruled`, quoting the ruling; the OCaml pin records the deviating
  reference, the Lean pin lem's semantics. Rulings record: X5 addendum in
  `2026-09-03_exception-case-rulings.md`; DESIGN's deviation list.

## Plants (each test fails on the before-fix binary)

Before-fix binary: `Lem 2026-05-01` (a scratch build of `git archive
5dfcd25`, so no git hash in its version string), run with its own
`library/`, every run under `timeout 60`. Verbatim, from
`plants.log`/`plants-compile.log` of the scratch directory (paths shortened):

```
== (a) item 1: test_contextual_keywords.lem on base
  exit 1: File ".../test_contextual_keywords.lem", line 140, character 44:   Syntax error
== (b) new negative probes on base (accepted, or hung = plant)
  neg_record_field_mk: exit 0 after 2 s
  neg_record_field_casesOn: exit 0 after 1 s
  neg_record_width_128: exit 0 after 2 s
  neg_variant_width_128: exit 124 after 60 s
  neg_tyvar_type_param_collision: exit 0 after 2 s
  neg_recup_reserved_base: exit 0 after 3 s
== (c) item 5: test_wide_patterns.lem on base
  exit 124 after 60 s
== (e) item 8: -outdir Makefile/sub on base
  exit 2: mkdir: cannot create directory ‘Makefile’: Not a directory Fatal error: exception Sys_error("Makefile/sub/Test_misc.lean: Not a directory")
== (d) items 2/3/4: generate with base, then compile against LemLib
  gen test_records: exit 0
  gen test_tyvar_collision: exit 0
  gen test_mutual_record_order: exit 0
== Test_records (generated by 5dfcd25) compiled against LemLib:
Test_records.lean:148:2: error: unexpected token 'at'; expected command
== Test_tyvar_collision (generated by 5dfcd25) compiled against LemLib:
Test_tyvar_collision.lean:52:50: error: Application type mismatch: The argument
Test_tyvar_collision.lean:54:53: error: Type mismatch
== Test_mutual_record_order (generated by 5dfcd25) compiled against LemLib:
Test_mutual_record_order.lean:259:26: error(lean.invalidField): Invalid field `hb_lo`: The environment does not contain `Nat.hb_lo`, so it is not possible to project the field `hb_lo` from an expression
```

Reading: (a) item 1 fails to parse before the fix. (b) five of the six new
negative probes are ACCEPTED before the fix (the suite's `lean-negative`
phase would report "FAIL (accepted)"); the sixth, the 128-argument
constructor, hangs in the old layout printer (its derived one-line output
is the item-5 shape), so before the fix it is neither refused nor
generated. (c) the wide-pattern test times out before the fix (the
`lean-wide-patterns` phase fails with exit 124). (e) before the fix the
`mkdir -p` failure is ignored and lem dies later on the temp-file rename
with `Sys_error`; the `lean-outdir-refusal` phase's grep for "cannot
create the output directory" fails. (d) the three extended positive tests
generate before the fix but their Lean does not compile: the bare `at`
field, the captured type variable, the unparenthesised update base. After
the fix every one of these is green in the suite run below. Item 10 is a
registration, not a fix: the probe's two pins are the before and after of
nothing; its plant is the suite's own rule that a registered probe which
PASSES fails the suite.

## Gates (verbatim tails)

All runs in the worktree, final binary (`lem -v`: see the suite's
`test_version` line), nothing rebuilt during a run (the first drift run
was invalidated by a concurrent rebuild — its fork side reported
`LEMROOT/lem: No such file or directory` — and re-run).

`scripts/ce make nonlean-regress` (tail, verbatim):
```
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
```

`scripts/ce env UPSTREAM_LEM=/home/dev/projects/linksem-lean/deps/lem-upstream LINKSEM=/home/dev/projects/linksem-lean/worktrees/linksem-upstream CERBERUS=/home/dev/projects/cerberus-lean-proj/deps/cerberus-upstream make upstream-drift DRIFT_OUT=<empty dir>` (head and the class summary, verbatim; the 32 library code rows are all "comments/whitespace only"; `cerberus-ocaml` and `linksem-ocaml` are absent from the per-directory counts, i.e. byte-identical — the same state the output-niceness record §13 recorded for `131b922`):
```
upstream-drift: upstream 3802cb0, fork lean-backend-v0.1.0-alpha.1-49-g5dfcd25-dirty; clients compared: linksem cerberus
upstream-drift: 944 upstream files; 198 differ (list: .../drift2/differences.txt)
     26 backends/tex_all
     11 lib/coq
      7 lib/hol
     26 lib/html
      1 lib/ident.stdout
      7 lib/isa
     26 lib/lem
      7 lib/ocaml
     84 lib/tex
      3 lib/tex_all
library code files (OCaml/HOL/Isabelle/Coq):
  comments/whitespace only  lib/coq/lem_basic_classes_auxiliary.v
  [… 32 such rows, no code row]
make: *** [Makefile:60: upstream-drift] Error 1
```
(The non-zero exit is the script reporting the fork's accepted non-code
library differences, as in every previous record.)

`cd lean-lib && capped lake build`: `Build completed successfully (39 jobs).`
`make` leaves the tree clean apart from the intended changes (`git status`
at commit time).

`scripts/ce make -C tests/comprehensive lean` (tail, verbatim):
```
test_version: OK (untagged, exact annotated tag, dirty tag, post-tag, archive fallback)
  OK: missing lean_constants refused; intact library generates
test_failure_admission: OK (registered probe with compiler failure is red, not XFAIL)
=== Wide patterns generate within 60 s (layout printer regression tripwire) ===
  OK: test_wide_patterns.lem generated in 4 s
=== Output directory that cannot be created is refused loudly ===
  OK: refused: cannot create the output directory Makefile/sub: Makefile/sub: Not a directory
=== Generation: 72 passed, 0 failed, 0 skipped ===
  [comments, layout, text-fidelity gates: OK; lean-compile: 768 PASS lines, no error]
  OK (leg 1): panic prints the Incomplete Pattern message, then continues with default
  OK (leg 2): fail-stops (exit 134) under LEAN_ABORT_ON_PANIC=1
  OK (leg 1): untaken branches not evaluated
  OK (leg 2): the taken branch fail-stops with its message
  OK (leg 3a): lemRequireAbortOnPanic refuses with LEAN_ABORT_ON_PANIC unset (exit 2)
  OK (leg 3b): lemRequireAbortOnPanic refuses LEAN_ABORT_ON_PANIC=0 (exit 2)
  OK (leg 3c): with LEAN_ABORT_ON_PANIC=1 the check passes and the failure fail-stops (exit 134)
  OK (leg 4): each reached Assert_extra.fail panics (2 of 2; B8 never_extract)
single-evaluation: OK
  OK: compiled draw sequences hold
  OK: compiled consumer injection holds
  OK: compiled N-ary seed injection holds
  OK (leg 1): two sufficient fuels agree; insufficient gives the declared sentinel; callee starts from the full ambient
  OK (leg 2): loud exhaustion at an insufficient runtime fuel fail-stops (exit 134)
  OK: compiled fuel x reader x mutual composition holds
  [lean-negative: 115 probes "OK (rejected as declared)", the six new ones included; lean-invariance: 10 witnesses "artifacts byte-identical across ocaml/hol/isa/coq"]
parity: 49 probes: 38 OK, 11 XFAIL (registered, Lean side pinned), 0 FAIL
=== No sorry/admit/axiom/native_decide in fuel_measure proofs modules (gate) ===
  OK: 11 proofs modules scanned; no sorry/admit/axiom/native_decide/bv_decide token
=== No fuel numerals in LemLib or generated code (gate) ===
  OK: 322 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
suite exit 0
```
(Bracketed lines are derived summaries of blocks of identical OK lines; every
other line is verbatim. The parity count is 38 OK + 11 XFAIL: the ten
registered probes before this slice plus `p_user_ord_minmax`.)

## Consumer trees

Both frozen consumers regenerated with the final `lem` of this branch and
compared with the trees generated by the unmodified `5dfcd25` binary from
the same inputs: Cerberus 170 files, linksem 194 files, **byte-identical**
(`diff -rq`: 0 differing files; `tokdiff.py`: identical). No census was
needed. This is expected: every change either refuses input that failed
today, renames or escapes only on collisions neither consumer has, or
(the layout printer) makes the same decisions faster.

## Files

- `src/parser.mly` (item 1), `src/lean_layout.ml` (item 5),
  `src/process_file.ml` (item 8), `src/lean_backend.ml` (items 2, 3, 4, 6,
  8, 9).
- Tests: `tests/comprehensive/test_contextual_keywords.lem`,
  `test_records.lem`, `test_mutual_record_order.lem`,
  `test_tyvar_collision.lem` (new), `test_wide_patterns.lem` (new),
  `negative/neg_record_field_mk.lem`, `neg_record_field_casesOn.lem`,
  `neg_record_width_128.lem`, `neg_variant_width_128.lem`,
  `neg_tyvar_type_param_collision.lem`, `neg_recup_reserved_base.lem`
  (all new), `parity/probes/p_user_ord_minmax.lem` + its two pins,
  `parity/expected_failures.txt`, `lean-test/lakefile.lean` (two roots),
  `Makefile` (phases `lean-wide-patterns`, `lean-outdir-refusal`).
- Docs: `DESIGN.md`, `TODO.md` (37 closed; 45–48 added), `RECORDS.md`,
  `2026-09-03_exception-case-rulings.md` (X5), `doc/manual/backend_lean.md`.

## Left for the operator

- Item 7's general fix waits on the `BEq` bridge design pass (TODO 45/46).
- TODO 47: whether type-definition parameters should be renamed rather
  than refused, and whether to narrow the `below`/`brecOn` field refusal to
  recursive records.
- Package C (cleanup, no output change), including the walker
  consolidation the item-3 collector adds to (TODO 48).

## Provenance

[USER 2026-10-03]: the rulings quoted above. [AGENT] (this worker): every
measurement, the escape/refuse split of item 2, the rename/refuse split of
item 3, the primed fresh names, the reserved `lemRecBase`, the 127-field
limit as a count, the item-7 disposition, the tests and this record.

## Orchestrator verification of package A (2026-10-03)

The orchestrator re-ran the gates independently on `f33cf4f`, from the
frozen inputs (Cerberus `51a7402ce`, linksem `f54d119` source export):
```
base make exit 0 / arc make exit 0   [tree clean after make]
cerb: 0 differing files / linksem: 0 differing files   [vs 5dfcd25's lem]
lemlib exit 0  (Build completed successfully (39 jobs).)
=== Generation: 72 passed, 0 failed, 0 skipped ===
Build completed successfully (206 jobs).
parity: 49 probes: 38 OK, 11 XFAIL (registered, Lean side pinned), 0 FAIL
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
upstream-drift: 944 upstream files; 198 differ   [library code rows all comments/whitespace only; cerberus-ocaml / linksem-ocaml absent]
```

**Rulings since the slice began**, all [USER 2026-10-03]:
- #2 (the `BEq` bridge): "(a) 450/400 (Recommended)", landing as its "Own slice
  after A and C". Design note: branch `docs/beq-lattice-design`, `39c4e0c`.
  TODO 45 (`automatic` termination under the bridge) is retested in that
  slice.

**Attribution note.** "Agree, this is minor but lets get it right from now
on": `Co-Authored-By` trailers name the model that actually did the work.
- `f33cf4f` correctly says Claude Fable 5.1.
- The earlier Fable-written output-niceness commits `ac5565b`, `131b922` and
  `0885bf6` say Claude Opus 5.5, because the orchestrator's brief prescribed
  that line. They are merged and pushed, so they stay as they are; this note
  is the correction.
