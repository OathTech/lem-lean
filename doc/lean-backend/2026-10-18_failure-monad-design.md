# Failure as an explicit result — revised design, 2026-10-18

[USER 2026-10-18] Design pass only; no production/consumer edits.
[AGENT 2026-10-18] Review `f91761f` invalidated `d60581a`'s indexed relation.
This revision replaces it and clarifies effects. Backend base: `b25be8b`.
**STOPPED on the initializer ruling in §5; not ready for implementation.**

## 1. Translation

Normalize strict computations before target macros in `main.ml:transform_for_target`.
Preserve binds through inlining, representation expansion, patterns and record
updates; `lean_analysis_prepass_all` is too late to recover erased arguments.

Use `Except Failure`, separating model failure from exhaustion. Initially lift
function values uniformly: `V(A→B)=V(A)→Except Failure (V B)`. Stage contracts,
canonical data/dictionaries and imported signatures determine types. See the
[contract appendix](2026-10-18_failure-monad-contracts.md), §§1–3.

Resolve reader/supply demands and typed fuel stages before effect closure.
Seed generated zero arms: exhaustion errors contribute failure; successful
sentinels/kills do not. Track supply dependencies separately. Failure freedom
never authorizes erasure/reordering; initially preserve all strict binds.

Preserve selected matches, unused/unit bindings and closure-construction stages.
Ordinary arguments evaluate right-to-left; strict Boolean partial applications
remain distinct from short-circuit forms. Library callback schedules are
contracts: `List.map` traverses a short list backwards; beyond 5001 elements
it evaluates the suffix forwards before unwinding the prefix.

Reader binders, captured/decremented counters and unrelated calls' ambient fuel
remain explicit. Retain existing supply-composition refusals; the staged-measure
support limit remains proposed. OCaml output stays unchanged.

## 2. Runners and proofs

ND forcing returns failure or an action/state pair. Construction, forcing and
traversal have separate contracts. NDnd visits siblings left-to-right but
accumulates successful lists in reverse. First abort discards outcomes/final
model state; supply retains consumed state and trace interfaces retain their
specified prefix. C-TF1 model-stop kills and typed fuel outcomes stay disclosed
compatibility exceptions (§4).

Replace indexed arrows with ordinary related-input success relations and
mutually inductive relations for strictly positive recursive data. Application,
bind, twice-invoked callbacks, returned higher-order closures and recursive ND
suspensions have small kernel witnesses. Complete runner correspondence remains
unproved (§6). A Lean recursive-result representation issue and its checked
conversion are disclosed in §4.

Keep Reference/Exec separate. Migrate complete-result measure equations; make
caesium execute discarded `step_ctx` work and prove full-result coverage; require
SL no-abort adequacy. Never weaken claims by omitting errors. TODO 13 stays open.
Churn: XL. Cerberus `049eb9a0a` inventory: 268 generated `lemSeq` sites/34 modules,
two copied proof references, 63 sufficiency declarations/15 carriers.

## 3. Evidence

After sourcing the project environment, baseline/spike reproduction commands:

```sh
CERB_MEM_MAX=16G scripts/capped make
make -C tests/comprehensive lean
python3 doc/lean-backend/failure-monad-spike.py build
CERB_MEM_MAX=16G scripts/capped python3 doc/lean-backend/failure-monad-spike.py measure --count 30000000 --repeats 6
```

Historical unchanged-backend baseline; not rerun for this revision:
```text
=== Generation: 74 passed, 0 failed, 0 skipped ===
parity: 49 probes: 38 OK, 11 XFAIL (registered, Lean side pinned), 0 FAIL
```

Corrected spike's derived seconds, unchanged since `d60581a`:
```text
success current: wall median=2.714583 range=2.698971..2.758259; cpu median=2.705; max_rss_kb=8628
success prototype: wall median=1.792342 range=1.768152..1.830307; cpu median=1.780; max_rss_kb=8732
failure current: wall median=3.819506 range=3.802355..4.407558; cpu median=2.735; max_rss_kb=8620
failure prototype: wall median=1.794701 range=1.765485..1.842109; cpu median=1.785; max_rss_kb=8656
```
Both loops select/apply callback 2 each iteration. Six alternating pairs/mode;
compilation excluded. Zero-work success medians: 0.002835/0.002828; failure:
1.073542/0.003380. Abort latency is noisy. Review `f91761f` independently
reproduced the corrected benchmark. Whole-driver cost remains unmeasured.

New contract witnesses: 19 empty axiom lists and fresh kernel replay, exit 0.
Source, commands and scope are in appendix §8.

## 4. Remaining limits

Full backend correspondence, runner proofs and consumer migrations are not
implemented. Other proposed rulings remain uniform lifting, explicit boundary
contracts, staged-measure refusals, retained C-TF1 exceptions and preserved claim
strength. Inherited quotation locations and baseline warnings remain disclosed
in appendix §7; the separate consumer-agent list remains unlocated.

## 5. Operator ruling needed: initialization

The blanket reader/fuel initializer refusal would reject existing positive
tests and three confirmed Cerberus module values. Withdraw that proposal.
Recommend explicit context-parameterized initialization, once per environment:
retain sources, migrate Lean exports/tests to projections, initialize a fresh
environment for a new context, and never silently reinitialize at `reader_seed`.

This changes today's per-use context lifting. Approve that compatibility policy,
or choose a narrower profile with named regressions? Appendix §5 gives concrete
cases and migrations. Charter §3 requires stopping here for this fuel/reader
ruling; further design work waits for the operator.
