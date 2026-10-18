# Failure as an explicit result — design, 2026-10-18

[USER 2026-10-18] authorized design/measurement only. Base: `b25be8b`. Recommendations: [AGENT 2026-10-18]. Keep OCaml byte-identical.

## 1. Analysis and representation

Use `Except Failure α`, distinguishing model-failure/exhaustion, preserving messages. Infer immediate/latent arrow, callback and field effects by monotone constraints over recursive components/imported libraries. Seeds: failwith-mapped constants, undefined/incomplete matches, partial primitives, comparison residuals, failure sentinels. Unknown callbacks are fallible. Reuse `lean_thread_scan_exp` (:3387), `lean_analysis_prepass_all` (:3727), reader/fuel fixed points (:1193/:1243/:1540); constant-reference sets miss callback effects. References: `src/lean_backend.ml` at base.

Proposed Lean-only declarations: `failure_signature val f = <arrow-effects>` classifies `target_rep`/`ground_rep`; `failure_rep val f = <typed-name>` supplies its lifted implementation. Pure contracts require total, seam-free dependencies; unclassified raw/infix reps refuse. Fallible comparisons need effectful dictionaries/set/map operations. Diagnostics need trace/state or refusal. No new unsafe/extern/implementation overrides/axioms.

Translate data structurally and arrows recursively: `V(A→εB)=V(A)→Cε(V(B))`, `Cpure(T)=T`, `Cfail(T)=Except Failure T`. Join effects conservatively; adapt pure callbacks with `.ok`. Preserve application stages: effectful function-producing bodies return `Except Failure (…→…)`, preventing A3 eta-delaying failure. Partial recursion needs structural/fuel totality or refusal in the executable cone; otherwise divergence can disappear.

## 2. Emission and composition

Replace `lem_seq_out` (:7449; uses :7684/:7952) with binds, including discarded/unit/unused patterns. Bind scrutinees once; match only afterward; evaluate only the selected arm. Sequence application arguments right-to-left, then the head; preserve parenthesized application boundaries. Reuse `supply_thread_list` (:7038) and `supply_shortcircuit` (:6991): tuples/lists/constructors reverse positional order, records reverse declaration order; short-circuit operands stay conditional. Explicit module initialization binds top-level computations in source/dependency order, including unused ones; exports require its successful environment.

Fuse failure and supply sequencing into one traversal: `S→(Except Failure A×S)`, retaining state at failure. Readers keep their existing binder order and lexical seeding. Mutual workers retain decremented counters; unrelated calls retain ambient fuel. Classify zero payloads explicitly: panic exhaustion becomes `.error exhausted`; existing typed domain outcomes retain their semantics; unknown snippets refuse. Measures/hypotheses remain pure, with existing supply/measure refusals. Preserve source stages around `lean_hoist_tail_binders` (:4732); emit staged adapters around workers, not earlier evaluation.

Do not automatically merge failures into `Exception` or ND kills: handlers could recover, and ND could continue siblings after an oracle abort. Keep construction errors outside, and translate suspended callbacks/runner forcing to propagate the global error. Existing domain errors stay distinct. Monad-specific fusion requires a proved, explicitly accepted observation-preserving adapter.

## 3. Evidence

After sourcing the container environment:

```sh
CERB_MEM_MAX=16G scripts/capped make
make -C tests/comprehensive lean
python3 doc/lean-backend/failure-monad-spike.py build
CERB_MEM_MAX=16G scripts/capped python3 doc/lean-backend/failure-monad-spike.py measure --count 30000000 --repeats 6
```

Baseline (exit 0):
```text
=== Generation: 74 passed, 0 failed, 0 skipped ===
parity: 49 probes: 38 OK, 11 XFAIL (registered, Lean side pinned), 0 FAIL
```
Lean 4.32.2; derived timing summaries, seconds:
```text
success current: wall median=2.688894 range=2.666341..2.732412; cpu median=2.680; max_rss_kb=8704
success prototype: wall median=1.676661 range=1.652639..1.686582; cpu median=1.670; max_rss_kb=8660
failure current: wall median=3.783501 range=3.738998..3.864842; cpu median=2.705; max_rss_kb=8744
failure prototype: wall median=1.683629 range=1.653687..1.705898; cpu median=1.675; max_rss_kb=8588
```
Zero-work success medians: 0.002985/0.002797; failure: 1.076637/0.003223 (current/prototype). Abort latency contributes substantially.

[Source](FailureMonadSpike.lean)/[recipe](failure-monad-spike.py): `f_let_unused` exercises discarded fallible binds; six alternating binary pairs/mode, compilation excluded. Workload: successful checks then terminal success/failure, not repeated recovery. Five prototype probes match failure pins/success controls; A5 repairs would be XPASS. Three proofs passed axiom census/fresh replay. Delete `lemSeq`/`lemSeqImpl` after all uses/hidden effects migrate.

## 4. Proof migration

At Cerberus `049eb9a0a`, derived textual counts: 268 generated `lemSeq` occurrences/34 modules; two staged proof references; 63 measure-sufficiency declarations/15 carriers. Reproduce using `rg -n -o '\blemSeq\b' lean_frontend/generated` and `rg -n '^theorem .*measure_sufficient' lean_frontend/*lemMeasureProofs.lean`; distinguish generated headers from copied seams.

Retain reference twins and success correspondence ([USER 2026-09-05], consumer `docs/2026-09-05_orchestrator-handoff.md:132`): `f_exc xs=.ok v→f xs=v`, generalized structurally for transformed functions/data. Reference-only twins inline logical `lemSeq`; never execute them. Failure correspondence needs differential checks. Sufficiency compares complete results; preserve wrapper `rfl` pins. Replace `lemSeq` simplifications with bind equations/reachability facts. Order: library contracts → twins/certificates → seams/runner → carriers → consumer theorems → pins/boundary removal. Kernel replay/axiom censuses gate proofs. Churn: L, potentially all 15 carriers plus consumer exports; no measured edit count. TODO 13 remains open.

## 5. Operator decisions

- Effect policy? Recommend staged `Except`, explicit contracts and totality refusals.
- Domain monads? Keep aborts distinct from UB/refusal/kills; fusion requires proved adapters.
- Migration? Require success certificates, failure differentials and consumer migration before seam deletion.

Unresolved: separate consumer-agent list unlocated (published disclosure read); inherited quotations/warnings unchanged under scope.
