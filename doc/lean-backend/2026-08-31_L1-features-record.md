# L1 feature-slice record — 2026-08-31

Provenance: L1 worker slice of the effect-retirement arc (charter:
cerberus-lean `lean_frontend/docs/2026-08-31_effect-retirement-design.md`
@ 913ee31d1, §8.1 L1; S0 record read — its S0-F1 finding concerns C1's
migration design, not these backend features' semantics; L0 base
4fd4d50). Branch `arc/effect-retirement`. All decisions [AGENT] unless
marked; quoted outputs are verbatim; tallies marked "derived" are
derived. `runEffectful` and the `effectful` class are deliberately
UNTOUCHED (they die in L2); the LemLib axiom cluster is untouched.

## Commits

| Feature | Commit | Charter | Disposition |
|---|---|---|---|
| 1. Supply lifting (`declare {lean} supply val`) | 383b996 | §3.2 | BUILT, full battery green |
| 2. `reader_consumer` (`declare {lean} reader_consumer val`) | 195b683 | §4.2 | BUILT, full battery green |
| 3. Per-declaration fuel budgets (`declare {lean} fuel val f = N`) | 40df3a8 | §8.3 | BUILT, opt-in constraint held structurally |
| — | (this record's commit) | — | record + late G-infix probe |

## Feature 1 — supply lifting: spec conformance (charter §3.2)

Mechanism as specified: state-passing (supply-threading) transform on
the reader-lifting pipeline — declare (contextual-keyword grammar row,
L0 mechanism, no new hard keyword) → typecheck `supply : Targetset.t`
on `const_descr` → `lean_supply_prepass` fixpoint over the call graph
at Val_def granularity (persisting across modules; instances skipped;
threading ARITY recorded per liftable cref) → threaded emission.

- **Annotation surface**: `declare {lean} supply val f`,
  target-scoped; G-type enforces `f : unit -> nat` (also accepts the
  synonym-mapped `natural`; noted below). No `supply_seed` built (v1,
  per spec: fail-closed minimalism).
- **Signature transform**: binder order [Inhabited] → readers →
  `(_lemSupply_<name> : Nat)` per supply (sorted-name order) →
  original params; result type becomes `((τ) × Nat …)` — one `× Nat`
  per supply, same order. Verified by TestSupplyCheck signature pins.
- **Body transform**: `supply_thread`/`supply_block` A-normalize
  draws, threaded calls, and control forms in LEFT-TO-RIGHT
  DEPTH-FIRST order (charter O1); a draw is
  `let (v, s') := LemLib.supplySplit s` (`supplySplit s = (s, s+1)` —
  the ONE LemLib addition: a plain def, kernel-transparent, no
  axiom/IO; the axiom cluster untouched). If/match arms return the
  value×states pair; only the taken branch consumes (pinned).
- **O7 determinism is structural**: the transform emits let-bindings,
  tuples, `supplySplit`, and the source's own control forms; no
  nondeterminism constructor exists anywhere in its emission (stated
  in the code header, DESIGN.md, and checkable by reading
  `supply_thread` — there is no ND builder to grep). [derived check:
  `grep -c 'ND\.' src/lean_backend.ml` = 0.]
- **Seeding**: entry points pass the initial value explicitly and
  receive the final value in the returned pair (no baked seed — the
  shape (b) the charter's entry decision consumes).
- **St discipline**: all new state in `St` with lifetime classes —
  `supply_lifted`/`supply_arity`/`supply_params_cache` [invocation],
  `supply_binder`/`supply_name_counter`/`supply_head_ok` [render] —
  wired into `St.reset_invocation`. NO new process-global refs; the
  `on_cr_simple_applied` class was not added to.
- **Compositions** (all spec'd, all tested): reader (binder order
  defined + pinned), reader_seed (seed defs ARE supply-liftable — the
  mini_pipeline shape; seed-name reader injection + supply binder
  coexist), fuel (worker threads the supply through the decremented
  self-call; the zero-fuel arm returns the sentinel with the supply
  UNCONSUMED; wrapper type gains supply arrows), multi-supply
  (independent streams, sorted order), and the tuple-let path rides
  the L0 single-RHS emitter (below).
- **Effectful mix**: `supply`×`effectful` on one val is a
  generation-time error (transitional rule; probe).

**Guard inventory → negative probes** (each probe asserts its declared
error fragment; suite `lean-negative`):

| Guard | Error fires at | Probe |
|---|---|---|
| G-λ (draw/lifted use under lambda) | transform | `neg_supply_lambda.lem` |
| G-bare (bare lifted/supply reference; incl. HOF) | transform + net | `neg_supply_bare.lem` |
| G-inst (instance method) | Fun_def/Let_def guard | `neg_supply_instance.lem` |
| G-rel + net (indreln/lemma/assert/non-threaded reach) | exp net (App/bare/Infix legs) | `neg_supply_indreln.lem` |
| G-arity (supply const arity; exact threading arity at calls) | transform | `neg_supply_arity.lem` |
| G-infix (lifted/supply constant infix) | transform + net | `neg_supply_infix.lem` |
| G-type (supply val not `unit -> nat`) | param sweep | `neg_supply_type.lem` |
| mix (supply × effectful/reader/reader_seed) | param sweep | `neg_supply_mix.lem` |
| truly-mutual block (v1 restriction, extend-on-need) | Fun_def guard | `neg_supply_mutual.lem` |
| reserved `_lemSupply` binder prefix | reserved-name contract | `neg_supply_shadow.lem` |

Multi-clause note: the >1-clause group guard exists as a fail-closed
backstop but is UNREACHABLE from lem source — the pattern compiler
folds multi-clause defs into one match before the backend, and the
compiled match THREADS CORRECTLY; converted to a positive case
(`clausy` in test_supply.lem, pinned). Not a deviation: the charter
never required rejecting multi-clause sources.

**Tuple-let single-evaluation (brief item e).** Expression-level
destructuring over a drawing RHS threads through ONE binding
(`destructure_once`, pinned: third draw is s+2 — a duplicated RHS
would give s+4). Top-level multi-name destructuring rides L0's
single-RHS emitter: one `private def lemLetRhs_*` (threaded) + one
threaded call per projection — within a call the RHS draws exactly
once (`top_a 500 = (500, 502)`: two draws, not four). Semantics note
(deliberate, documented): a supply-lifted top-level VALUE binding
becomes a function of the supply, so each projection call re-runs the
RHS with its caller's supply — the state-passing semantics of a
drawing value binding, deterministic and pinned; the effectful
mechanism's once-at-init semantics is not claimed for it.

## Feature 2 — reader_consumer: spec conformance (charter §4.2)

As specified: `reader_consumer : Targetset.t` on `const_descr`;
consumer uses count as reader uses in the lifting fixpoint (callers
lift); call sites pass ALL reader parameters as extra leading
arguments in the global sorted order, injected exactly once via the
bare-Constant repair `(rep _lemReader_…)`; bare/HOF references repair
by type-preserving partial application; **injection routes through
`reader_inject_name`**, so inside a `reader_seed` def the SEED's first
argument is picked up with no new machinery — probe-verified emission:

    def  seedy  (cfgv : Nat) (x : Nat)  : Nat := ( RCImpl.scaled cfgv)  x

**Guard inventory → probes**: RC-rep three legs (missing rep
`neg_rc_norep.lem`; parameter-binding rep `neg_rc_paramrep.lem`;
non-simple forms — same sweep, message "unsupported Lean target_rep
form"); RC-mix `neg_rc_mix.lem` (× reader/reader_seed/supply/
effectful, one sweep); RC-inst `neg_rc_instance.lem` (via the
extended `exp_needs_reader` + the existing instance guard); RC-rel/
scope `neg_rc_indreln.lem` (any consumer call without a reader value
in scope — indreln, lemmas/asserts, non-lifted contexts). Plus an
infix-position rejection in ordinary emission and a consumer-head
case in the supply transform (consumer calls with supply-drawing
arguments inject readers correctly).

Finding (positive, recorded): an infix USE of an operator-named
consumer arrives at the backend as an App node (lem decomposes rep'd
operator applications), and injects CORRECTLY —
`(RCImpl.op _lemReader_cfg) a 2` (probe-verified); the Infix-node
guard is a backstop with no lem-source reproducer found.

Tests: `test_reader_consumer.lem` (plain/lifted/seed/bare-HOF
contexts; the seed-rooted entry is .lem-assertable and asserted),
`TestReaderConsumerCheck.lean` (rfl pins), compiled
`TestReaderConsumerExec.lean` (phase `lean-reader-consumer`),
`invariance/inv_reader_consumer.lem`.

## Feature 3 — fuel budgets: spec conformance (charter §8.3 + brief)

Syntax `declare {lean} fuel val f = <N>` (numeric Num row beside the
backtick sentinel row; LR conflict counts unchanged). Attachment
exactly per the review's map: one `Targetmap` field (`fuel_budget`)
beside `fuel_sentinel` → typecheck `Decl_fuel_budget` case →
`fuel_budget_for` consulted at ONE place, the wrapper emission,
replacing the literal ` lemDefaultFuel` only when a budget is
declared. Workers, threading, self-call discipline untouched.

**THE HARD CONSTRAINT (consumer-ratified, §8.3) HOLDS STRUCTURALLY:**
unannotated declarations emit the identical ` lemDefaultFuel` text —
the only code path difference is `match fuel_budget_for c with None ->
" lemDefaultFuel"`. Witnessed three ways: (i) the pre-existing corpus
tree-diff (below) is byte-identical; (ii) probe: an unannotated
sibling in the same file emits `dspin_lemFuel lemDefaultFuel`
verbatim; (iii) the compiled boundary test (below) shows the
unannotated sibling cutting at exactly 10^6. No stop-and-report was
needed.

Guards → probes: budget without sentinel (`neg_fuel_budget_nosentinel.lem`),
non-positive budget (`neg_fuel_budget_zero.lem`); both swept for every
budget-marked constant even if unused. The human-target echo emits
the plain literal (round-trips; the m1 echo discipline). L0's
`lemDefaultFuel` reserved-def-name guard already protects the default
reference. Compositions: reader (`climb`, budget 7, wrapper keeps the
reader-prefixed type) and supply (`fuel_draws_b` in test_supply.lem,
budget 3 — exhaustion mid-stream returns the partial draw list with
the supply at the cut, pinned).

## Compiled-test evidence (verbatim, at 40df3a8 + the record commit's probe)

`tests/comprehensive/lean-test/.lake/build/bin/test-supply-draws`:

      ok: draw_two 100 () = ((100, 101), 102)
      ok: destructure_once 30 () = ((30, 31, 32), 33) [RHS draws once]
      ok: top_a 500 = (500, 502) / top_b 500 = (501, 502) [projections: one RHS call each]
      ok: uses_both 9 40 3 = (52, 41) [reader x supply]
      ok: uses_seeded 40 3 = (85, 41) [reader_seed x supply]
      ok: fuel_draws 60 2 = ([60, 61], 62) [fuel x supply]
      ok: fuel_draws_lemFuel 1 60 2 = ([60], 61) [exhaustion leaves supply at cut]
      ok: two_streams 10 100 () = ((10, 100, 11), 12, 101) [independent streams]
    supply draws: OK
    exit=0

`test-reader-consumer`:

      ok: uses_scaled 9 3 = 903 [lifted caller injects]
      ok: uses_scaled_and_cfg 9 3 = 912 [consumer + direct read]
      ok: maps_scaled 9 [1,2] = [901,902] [HOF partial application]
      ok: via_seed 3 = 1407 [reader_seed pickup through consumer + lifted callee]
    reader_consumer: OK
    exit=0

`test-fuel-budget`:

      ok: bspin 4 = 0 [within budget 5]
      ok: bspin 5 = 999 [exhausts at budget 5]
      ok: dspin 999999 = 0 [unannotated runs to lemDefaultFuel]
      ok: dspin 1000000 = 999 [unannotated cuts exactly at lemDefaultFuel]
      ok: climb 10 4 = 10 [reader x budget: completes under 7]
      ok: climb 20 4 = 998 [reader x budget: exhausts at 7]
    fuel budget: OK
    exit=0

The elaborator/kernel pins (TestSupplyCheck.lean — `rfl` proofs of the
exact draw sequences, the charter-O1 order evidence — and
TestReaderConsumerCheck.lean) all elaborate in the suite build.

## Invariants at close (verbatim)

- Non-Lean regression net, at the final tree:

      nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)

  Re-run green after EACH feature commit; zero drift at every check —
  no stop-and-report event occurred.
- Pre-existing comprehensive corpus, generated by the L0-base lem
  (scratch build of 4fd4d50 via `git archive`) vs this slice's lem,
  sha-compared per file: first check (post-F1, 43 pre-existing tests
  = 86 .lean files) printed verbatim `TREE-BYTE-IDENTICAL`; the
  post-F2/post-F3 re-checks (84 files — `test_contextual_keywords`
  excluded after its SOURCE was deliberately extended with the two
  new words) reported zero `DIFF:` rows. No pre-existing generated
  file changed; the only corpus deltas are the new test files and the
  contextual-keyword test's own new rows.
- Full battery at the final tree:

      === Generation: 47 passed, 0 failed, 0 skipped ===
      Build completed successfully (134 jobs).
      FULL SUITE EXIT: 0

  incl. both panic-pin legs, the m7 and M2 pins, the three new
  compiled phases, and 32/32 negative probes (15 pre-slice + 11
  supply + 5 reader_consumer + 2 fuel-budget; every row
  `OK (rejected as declared)`).
- New `lean-invariance` phase (charter §6.3's non-Lean invariance
  test, built this slice): each `invariance/inv_*.lem` generated for
  ocaml/hol/isa/coq with and without its `declare {lean}` lines,
  byte-compared; verbatim:

      OK: inv_fuel_budget.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
      OK: inv_reader_consumer.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
      OK: inv_supply.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)

  Plant-tested both directions: a declare-free file →
  `FAIL (vacuous): inv_plant.lem contains no 'declare {lean}' lines`
  (exit 1); stripping a semantic line instead → FAIL with the diff
  rows (`Only in invariance/_out/decl: inv_supply.ml` …, exit 1);
  both plants reverted. (The echoing/human targets re-render declare
  lines by design and are covered by the L0 golden net instead —
  matching the L0 record's live-catch finding.)
- lean-lib: `Build completed successfully (35 jobs).` (capped). The
  ONLY LemLib delta this slice is `LemLib.supplySplit` (one plain
  def; justification: the charter names it as the draw primitive —
  greppable, kernel-transparent). The runEffectful axiom cluster is
  byte-untouched (dies in L2, not here).
- ocamlyacc at the final grammar, verbatim: `5 rules never reduced` /
  `2 shift/reduce conflicts, 2 reduce/reduce conflicts.` — identical
  to the L0 record's counts; both new words ride the contextual-
  keyword mechanism and are asserted usable as ordinary identifiers
  by the standing `test_contextual_keywords.lem` (rows added, sum
  re-pinned).

## Deviations / notes, flagged loudly

1. **Manual not rewritten.** Charter §6.3 lists "lem manual entry
   beside the reader declare"; the reader has NO manual entry — the
   manual (`doc/manual/backend_lean.md`) is the review's m5
   registered-stale item (its rewrite is a priced item of its own).
   All three features are documented where reader/fuel actually live:
   `doc/lean-backend/DESIGN.md` (new sections + declare-table rows).
   [AGENT] call; flag for the operator if the manual entry is wanted
   in-arc.
2. **Charter §6.3's "run before (against the effectful scaffold) and
   after … the swap"** describes the C1-side equivalence at the
   `symbol.lem` declare swap; it is not executable in L1 (no model
   swap here). L1's compiled tests pin the threaded semantics
   absolutely (exact sequences), and L0's m7 pin covers the effectful
   scaffold side; the before/after differential at the swap is C1's
   battery.
3. **G-type accepts `natural` as well as `nat`** (both map to Lean
   `Nat`); the charter says `unit -> nat`. Superset, documented in
   the guard message's spirit; flag for the reviewer.
4. **Supply-lifted top-level value bindings** have state-passing
   (per-use) semantics, not the effectful once-at-init semantics —
   deliberate, documented in DESIGN.md and in Feature 1 above, and
   irrelevant to the cerberus clients (all function defs).
5. **Defs carrying a Lean target_rep are excluded from supply
   lifting** (their bodies are dead text; their call sites emit the
   rep, which cannot take a supply). Deliberate divergence from the
   reader pre-pass (which lifts them), documented at
   `lean_supply_prepass`; the alternative silently injects state into
   a hand-written rep.
6. Scratch hygiene: `.l1-scratch/` (probes + the 4fd4d50 comparison
   build) is ephemeral and deleted at slice end; every load-bearing
   probe output is quoted verbatim here or committed as a test.
