# Independent review of the revised failure-monad design

[AGENT 2026-10-18] **Recommendation: revise before implementation.** The
proposed logical relation rejects a correctly translated higher-order function.
The effect analysis also needs an explicit contract for compiler-inserted fuel
failures and supply effects. The proposed initializer refusals remove existing
supported cases and need a concrete compatibility disposition before approval.

Reviewed revision: `d60581ae5db4a8b73218a31c960c4206cfd35b6d`, comprising the
short design, the complete contract appendix, and the reproducible spike. This
is a fresh full review, based on the revised documents and source inspection;
the earlier review's verdict was not used as evidence. Backend implementation
base: `b25be8b`. Consumer sources inspected: Cerberus `049eb9a0a`, caesium
`bb751136`, and cerberus-sl `68832d9`. No production or consumer changes are
part of this review.

## Findings

### 1. High: the finite-index arrow relation cannot certify ordinary callback application

**Location:** `2026-10-18_failure-monad-contracts.md:317–343`, particularly
the equation at lines 324–325 and the all-indices requirement at 328–330.

Take the source function `applyZero f = f 0` of type `(Nat → Nat) → Nat`.
Its correct executable translation is `applyZero' f' = f' 0`, of type
`(Nat → Except Failure Nat) → Except Failure Nat`. There is no recursion,
fuel, representation override, or actual failure in this counterexample.

With the stated unconstrained index zero, the callbacks `f = fun _ => 0`
and `f' = fun _ => .ok 1` satisfy `R(Nat→Nat,1)`: both argument and result
relations in that arrow clause are at index zero. But the required
`R((Nat→Nat)→Nat,2) applyZero applyZero'` then applies those callbacks and
demands `R(Nat,1) 0 1`, namely `0 = 1`. Thus the correctly translated
`applyZero` fails the proposed relation. Quantifying over all indices includes
this failing index; it does not repair it. Storing `applyZero` as a function
value also requires the problematic arrow relation, so moving a top-level
certificate to all-index arguments alone does not address the design's
callback-bearing data contract. Even if indexing is reserved for recursive
data, placing this function in a field of a positive recursive datatype
reintroduces the same counterexample. Interpreting base types as equality
even at index zero instead gives the analogous contradiction at index one.

[FailureMonadRelationCounterexample.lean](FailureMonadRelationCounterexample.lean)
formalizes exactly this fragment of the appendix. The theorem
`RelationCounterexample.applyZero_not_related` and the base-equality variant
have no axioms and passed fresh kernel replay. This is a counterexample to the
proposed proof interface, not a failure of the failure-monad approach itself.

**Required disposition:** revise the relation and establish its application /
composition lemma on a small example before treating it as the migration
contract. Possible directions include indexing an explicit computation
relation by the evaluation steps it consumes, or guarding recursive
observations while using an ordinary logical relation for nonrecursive arrow
types. A single decrement on an arrow followed by an unrestricted, completed
evaluation is insufficient. Check a callback invoked twice, a returned
higher-order closure, and an ND suspension carrying such a value against the
revised relation. These are small proof witnesses, not a request for a new
enumerative gate.

### 2. Medium: the effect rules omit effects introduced by fuel and supply lowering

**Location:** appendix lines 30–33, 72–82, 240–241, and 251–280.

The pipeline solves effects and then adds fuel/supply machinery. The supplied
rules initialize known recursive bodies at `0`, propagate explicit failure and
invoked-stage effects, and use the result to decide whether computations may
be erased or reordered. They do not say how generated zero arms participate
in the fixed point, or how absence of failure is separated from absence of
supply effects.

There are existing concrete witnesses for both obligations:

- `tests/comprehensive/test_fuel_param.lem:42–44` defines `loud_spin` using
  only a numeric test and recursion, with `fuelExhausted n` in its declared
  zero arm. Its source-body SCC has no failure seed under the listed rules,
  yet its executable translation must return an exhaustion error at fuel
  zero. `TestFuelParamCheck.lean:16,22` pins that zero stage today. In a
  discarded call, classifying this as erasable loses precisely the failure
  this design is meant to expose. Checking the original body for totality is
  insufficient: termination and absence of *budget exhaustion* differ.
- A total supply draw can never fail and still cannot be erased or reordered.
  For the `tick` of `tests/comprehensive/test_supply.lem`,
  `let _ = tick () in tick ()` started at supply `s` must return `(s+1,s+2)`;
  dropping the first call returns `(s,s+1)`. A failure-only `0` annotation does
  not justify that transformation. The existing supply analysis recognizes
  these calls, but the appendix does not state that its result is a necessary
  input to the advertised erasure/reordering criterion.

The earlier requirement for a total, effect-free certificate is a good
constraint; the concrete rules must explain how that certificate excludes
these two cases. This is a specification gap, not a claim that an implemented
optimizer has already made these changes.

**Required disposition:** seed each fuel stage from its translated zero
payload before effect closure (or explicitly re-solve after lowering), and
make supply dependence part of the no-erasure/no-reordering obligation.
Distinguish a successful typed kill or value sentinel from an error-producing
sentinel. The first implementation can simply preserve all such binds;
there is no need for a more elaborate effect lattice to authorize optimization
now. Pin one discarded zero-budget call and one draw-before-error example,
including the retained supply state.

### 3. Medium: the initializer support cut already breaks positive tests

**Location:** appendix lines 297–305; short design lines 96–99.

Refusing reader/fuel-dependent top-level values is an explicit proposal, so
the issue is not a hidden semantic change. The missing information is that
these are currently supported and tested inputs, rather than only hypothetical
future forms:

- `tests/comprehensive/test_fuel_param.lem:64`: `spun_value`; the existing
  `lean-test/TestFuelParamCheck.lean:60–62` checks its behavior at two fuels.
- `tests/comprehensive/parity/probes/p_fuel.lem:41`: the top-level `results`
  value calls ambient-fuel functions and feeds an existing parity lane.
- `tests/comprehensive/test_instance_reader.lem:64`: `sw_plus_one`, a
  top-level value reading the instance reader.

Consequently the new backend cannot both retain these accepted inputs and
apply the proposed blanket refusal. The previous baseline count is useful
historical evidence, but cannot be the unchanged acceptance expectation for
this proposal. Turning a value into `unit → T` is also not automatically an
OCaml-neutral migration: it moves initialization to invocation, which is
observable when the initializer can fail.

**Required disposition:** disclose the known affected cases in the support
decision and specify their migration/test disposition. Either authorize and
document the loss of support, or specify explicit context-parameterized
initialization with once-per-environment evaluation. Do not silently remove
positive tests or change source initialization timing to restore green tests.
Inventory actual consumer occurrences before committing to the support cut;
this review establishes the test regressions, not their whole-project count.

## Assessment of the rest of the design

The early normalization point is appropriate. `src/main.ml:278–294` precedes
target macros, whereas `src/process_file.ml:430` does not. Keeping binds
around value-variable substitution addresses the inline erasure reproduced
by the spike. Requiring the expanded OCaml schedule for OCaml-specific
inlines avoids inventing strictness at those boundaries.

Uniform function-value lifting is a coherent initial representation choice.
The appendix now separates canonical public arrows from boundary replacement
types, refuses unsafe coercions of higher-order arguments, and requires
module-level type/dictionary contracts. I support that direction, subject to
finding 1. Pure comparison adapters still need their promised totality
evidence; assigning a pure signature is not that evidence. Refusing an opaque
boundary with no usable contract is preferable to silently assuming purity.

The `List.map` schedule is correct for the inspected OCaml implementation.
Compiled OCaml and prototype traces agreed at lengths 3, 5001, 5002 and 5003;
the competing failure cases selected 3 and 5002 respectively. The distinction
between flat Boolean operators and parenthesized partial application agrees
with the existing `TestSupplyCheck.lean:61–72` contract. An additional small
compiled OCaml check of record updates confirmed base-first evaluation and
reverse field-declaration order even when source field order was swapped.
These conclusions concern the inspected compiler/library versions; scheduling
contracts must be revisited if those dependencies change.

The ND design distinguishes construction, forcing and traversal failures
usefully. Its sibling visitation and result accumulation match the explicit
binds in `ocaml_frontend/smt2.ml:75–82,117–132`: NDnd visits left-to-right but
prepends results, while NDbranch returns left results before right results.
The `liftND` put-before-action schedule matches the pair in
`frontend/model/nondeterminism.lem:276–280`. Discarding accumulated outcomes
on global failure, retaining only the specified diagnostic prefix, and
separating supply state from ND model state form a consistent policy.
Preserving C-TF1 kills and typed exhaustion kills as disclosed compatibility
exceptions is a reasonable recommendation. It does not establish parity for
the intentionally exceptional sites. The spike does not implement or validate
the new runner, so these are source-review conclusions, not runtime proof.

The consumer migration correctly avoids silently weakening claims. Caesium's
`DriverExecutionCompiler.lean:99–151` omits the discarded filter and proves its
old equation by unfolding `lemSeq`; the source filter really exists at
Cerberus `frontend/model/driver.lem:1379–1382`. Adding it to the program
denotation and proving complete-result new-to-new coverage is necessary.
Likewise the proposed no-global-abort obligation for the SL endpoint prevents
error runs from disappearing behind successful-list membership. Complete
measure equalities, the separation of Reference and Exec, and keeping TODO 13
open are the right requirements. Their feasibility remains unproved; in
particular, success correspondence cannot discharge the new no-abort claim.
The XL assessment is credible. An independent text recount confirmed 268
`lemSeq` occurrences in 34 generated modules, excluding the two copied proof
references, and 63 measure-sufficiency theorem declarations in 15 carriers.
Those counts remain inventories, not a measured proof-edit budget.

## Reproduction and measurement

All builds were local to the review worktree and memory-capped. Commands,
after selecting the project's OCaml environment:

```sh
CERB_MEM_MAX=16G scripts/capped make
python3 doc/lean-backend/failure-monad-spike.py build
CERB_MEM_MAX=16G scripts/capped python3 doc/lean-backend/failure-monad-spike.py measure --count 30000000 --repeats 6
cp doc/lean-backend/FailureMonadRelationCounterexample.lean .tmp/failure-monad/spike/RelationCounterexample.lean
cd .tmp/failure-monad/spike
CERB_MEM_MAX=16G ../../../scripts/capped lake env lean -o .lake/build/lib/lean/RelationCounterexample.olean RelationCounterexample.lean
CERB_MEM_MAX=16G ../../../scripts/capped lake env leanchecker --fresh RelationCounterexample
```

The root build and spike build exited 0. All five compiled probe checks passed
for failure prefixes and success inputs 1 and 7. The inline witness reproduced
the current successful 42 and the proposed error. The spike's six theorem
axiom outputs contained only `propext` and `Quot.sound`, or no axioms.
`lake env leanchecker --fresh FailureMonadSpike` exited 0. The review
counterexample module's two axiom lists were empty, and its fresh replay also
exited 0. The baseline still contains `failwithIImpl`, `lemSeqImpl`, and
`fuelExhaustedWithImpl` as unsafe implementation overrides in LemLib; the spike
imports that runtime and does not retire those boundaries. The counterexample
imports only `Init` and introduces no such overrides.

Fresh generated C has per-iteration `List_get!Internal` followed by
`lean_apply_1` in **both** timed loops (CurrentMain.c:111–112 and
PrototypeMain.c:115–116). The earlier dispatch asymmetry is absent. The
comparison measures this discarded-check workload, including replacement of
the old native sequencing seam. It does not isolate the cost of an `Except`
tag test, uniform currying, or a complete Cerberus execution.

The independent run exited 0: six alternating pairs per mode, 30,000,000
successful calls followed by one terminal call, with every expected exit,
checksum and failure-message check passing. Derived summaries from that run
(seconds):

| Mode | Current wall median (range) | Prototype wall median (range) | Current / prototype CPU median |
|---|---|---|---|
| Zero-work success | 0.003864 (0.002748–0.005947) | 0.004563 (0.003296–0.005041) | 0.000 / 0.000 |
| Zero-work failure | 1.077555 (1.075560–1.087454) | 0.005112 (0.004052–0.006972) | 0.000 / 0.000 |
| Success | 2.858401 (2.835891–2.916084) | 1.834490 (1.798788–1.912600) | 2.845 / 1.825 |
| Terminal failure | 3.874786 (3.841815–3.912304) | 1.827774 (1.819515–1.870239) | 2.795 / 1.820 |

This reproduces the direction and approximate scale of the revised results.
The zero-work failure control exposes roughly a second of current-binary
abort latency, which is not monadic propagation cost. The design appropriately
withdraws the old comparison and limits its new claim. Whole-driver cost,
deep propagation and callback-rich uniform lifting remain unmeasured; keep
the bounded driver measurement in the implementation charter.

The comprehensive suite and consumer build/differential ladders were not rerun;
no backend or consumer implementation was changed. The original baseline in
the design is not presented here as independently recertified. Existing
compiler warnings were visible in the rebuild, including OCaml nonexhaustive
matches/deprecation alerts and generated Lean unused-variable warnings. They
remain findings in the existing baseline, not a warning-free result or a
request to suppress them.

The inherited attributed quotations reported by the appendix are still present
in Cerberus `lean_frontend/VALIDATION.md:292` and LemLib seam comments. They
were not copied into this review or edited; their removal is for the owner to
decide. Rebuildable generated files, measurements and build caches from this
review are removed after recording the conclusions.
