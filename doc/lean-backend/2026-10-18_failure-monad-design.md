# Failure as an explicit result — revised design, 2026-10-18

[USER 2026-10-18] Design pass only; no production/consumer edits.
[AGENT 2026-10-18] Supersedes `a331435` after review `9a9b409` found incomplete
contracts and confounded timings. Backend base: `b25be8b`.

## Translation

Normalize strict computations **before** target-specific transformations in
`main.ml:transform_for_target`, preserving explicit binds through inlining,
representation expansion, patterns and record updates. The old
`lean_analysis_prepass_all` hook runs too late. The inline witness demonstrates
the erased argument; scanning the surviving tree cannot recover it.

Use `Except Failure`, distinguishing model failure from exhaustion. Initially
lift every function value uniformly: `V(A→B)=V(A)→Except Failure (V B)`.
Pure callbacks receive recursive source translation, not an opaque higher-order
coercion. A two-point immediate-effect analysis governs computations;
stage signatures, canonical recursive data/dictionaries and versioned imported
contracts determine types without effect polymorphism. See the proposed
[contract appendix](2026-10-18_failure-monad-contracts.md), §§1–2, for rules,
actual declaration syntax, primitive types and refusals.

Binds preserve discarded/unit/unused lets, selected matches and function-producing
stages. Ordinary argument evaluation is right-to-left; source application groups
and strict Boolean partial applications remain distinct from short-circuit forms.
Library contracts additionally specify callback scheduling. In particular,
`List.map` evaluates a short list backwards, but after 5001 elements evaluates the
remaining suffix forwards before unwinding the prefix. A generic `mapM` is wrong.

Reader bindings and ambient/decremented fuel policies remain. A function-valued
zero payload preserves its invocation stage. Initializer environments preserve
unused top-level computations and dependency order. Existing supply composition
refusals remain; additional staged-measure and context-dependent initializer
refusals are explicit proposed support limits (§5). OCaml output stays unchanged;
no new unsafe code, externs, implementation overrides or axioms are proposed.

## Runners and proofs

ND suspensions return `Except Failure (Action'×State)`; supply separately retains
its state on error. Runner signatures and equations in §4 distinguish action
construction, forcing and traversal. NDnd siblings execute left-to-right while
successful result lists accumulate in reverse branch order. First abort stops
traversal and discards accumulated outcomes/final model state; trace interfaces
retain their specified prefix. C-TF1 model-stop kills and typed fuel outcomes
remain named compatibility exceptions, not ordinary UB or global aborts.

Reference/Exec packages stay separate. All-index logical relations cover related
callbacks/data and successful ND observations (§6). Success certificates alone
cannot transfer unconditional consumer claims. Migrate complete-result measure
equations; make caesium's program execute the discarded `step_ctx` work and prove
new full-result coverage; prove no-global-abort alongside SL adequacy. A missing
proof blocks the claim rather than filtering errors out of outcomes. TODO 13 stays
open. Kernel replay and axiom censuses remain proof gates.

Churn estimate: **XL**, including ND/state/runner APIs, relations and consumer
theorems. Recount at Cerberus `049eb9a0a`: 268 generated `lemSeq` occurrences/34
modules, two copied proof references, 63 sufficiency declarations/15 carriers.
These are inventories, not measured edits. Migration order: contracts → twins/
types → seams/runners/certificates → carriers → consumers → pins/seam removal.

## Evidence

After sourcing the container environment:

```sh
CERB_MEM_MAX=16G scripts/capped make
make -C tests/comprehensive lean
python3 doc/lean-backend/failure-monad-spike.py build
CERB_MEM_MAX=16G scripts/capped python3 doc/lean-backend/failure-monad-spike.py measure --count 30000000 --repeats 6
```

Original unchanged-backend baseline, not rerun during revision:
```text
=== Generation: 74 passed, 0 failed, 0 skipped ===
parity: 49 probes: 38 OK, 11 XFAIL (registered, Lean side pinned), 0 FAIL
```

Derived seconds:
```text
success current: wall median=2.714583 range=2.698971..2.758259; cpu median=2.705; max_rss_kb=8628
success prototype: wall median=1.792342 range=1.768152..1.830307; cpu median=1.780; max_rss_kb=8732
failure current: wall median=3.819506 range=3.802355..4.407558; cpu median=2.735; max_rss_kb=8620
failure prototype: wall median=1.794701 range=1.765485..1.842109; cpu median=1.785; max_rss_kb=8656
```
Zero-work success medians: 0.002835/0.002828; failure: 1.073542/0.003380 (current/prototype).
Both C loops select/apply callback 2 each iteration. Six alternating pairs/mode,
generation/compilation excluded, zero-work success/failure controls. This is a
shallow microbenchmark, not whole-Cerberus or deep-propagation cost. The old
comparison is withdrawn. Compiled witnesses reproduce inline erasure and
OCaml map order around the threshold. Six proofs passed axiom census and fresh
`leanchecker --fresh FailureMonadSpike` replay (exit 0).

## Operator decisions and limitations

- Approve uniform function-value lifting and explicit boundary contracts?
  Recommend yes initially; optimize only after correspondence.
- Approve the named initial refusals? Recommend yes rather than moving effects.
- Move C-TF1 kills to aborts? Recommend preserving the accepted behavior separately.
- Preserve consumer claim strength? Require complete-result coverage and no-abort proofs.

Inherited quotation locations: consumer `VALIDATION.md:292` and LemLib's seam
comments. Existing baseline warnings remain out of scope. The separate consumer
agent list remains unlocated. §7 of the appendix dispositions all eight findings;
the revision still needs fresh independent review.
