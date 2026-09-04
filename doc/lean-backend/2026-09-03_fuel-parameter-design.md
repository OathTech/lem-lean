# Fuel as a quantified parameter — design note (2026-09-03)

Branch `arc/fuel-parameter` (lem-lean), paired with cerberus-lean
`arc/fuel-parameter` (the pin dance: lem merges first). Author: the
orchestrator [AGENT]; rulings [USER 2026-09-03] quoted verbatim. Status:
DRAFT for the refined-cerberus consumer review before either merge (the
fuel-arc practice, `cerberus-lean/lean_frontend/docs/2026-09-02_fuel-arc-design.md`).

## 1. The ruling

The refined-cerberus team found that the fuel design bakes in a budget.
[USER 2026-09-03]:

> "The correct way for this to work is that fuel is an execution
> parameter that 'doesn't matter' - that is, any fuel value can be
> chosen. The current design does this for the 'outer' loop but it bakes
> in a magic 10^8 value. This is wrong - this and all other magic values
> are completely forbidden. [...] The correct structure is for fuel to be
> a parameter which can be chosen as 10^8 or any other value when calling
> the interpreter."
>
> "All similar such magic values should be removed and replaced by
> quantified parameters"
>
> "magic values like this (or any similar 'magical' choices over
> nondeterminism) are absolutely completely forbidden and are
> definitionally bugs"

The principle is recorded in `DESIGN.md` ("No magic values") and in
cerberus-lean `lean_frontend/DESIGN.md` §4.

## 2. What is wrong today (measured 2026-09-03, cerberus-lean @ `de2fbf1bd`, lem-lean @ `0890229`)

| Constant | Where | Consumers |
|---|---|---|
| `lemDefaultFuel : Nat := 1000000` | `lean-lib/LemLib.lean:57` | the wrapper of EVERY fuel-declared function: 77 generated wrapper sites in 16 cerberus generated files (`def f … := f_lemFuel lemDefaultFuel`), ~12 explicit hand-written call sites in `CerbMem.lean` |
| per-declaration budget literal (``declare {lean} fuel val f = N``) | `src/lean_backend.ml` (≈:2163) | replaces `lemDefaultFuel` in one wrapper with `N`; used by cerberus's driver family to put `10^8` on it |
| `CerbFuel.driverFuel : Nat := 100000000` | cerberus `CerbFuel.lean:71` | `CerbND.ndDefaultFuel`, the runner leaves, nine `rfl` wrappers (`drive = drive_lemFuel driverFuel` …) |

Consequence: a program that exhausts an inner `lemDefaultFuel` budget
(a fuel-declared model function recursing more than 10^6 deep) cannot be
rescued by ANY choice of the outer fuel — the accepted fuel exception
("we could always just run the semantics with more fuel", [USER
2026-09-03]) is therefore false as implemented. The LemLib set/map recursions (`Pset.unionGo/interGo/diffGo/subsetGo`,
`compareAux`, `Pmap.merge`, the closure `tc`) run on budgets computed
from the data (`height s1 + height s2 + 1`, `cardinal + 1`, `(2n)^2 +
1`), and `Pset.lfp` on a budget its caller supplies. [USER 2026-09-03],
verbatim: "the lemlib bounds are fine if they are passed as parameters
to the semantics and can be chosen by a calling context. Otherwise they
are forbidden magic values." So a bound computed inside the definition
is NOT exempt: each of these either (a) takes its fuel from the same
ambient parameter as everything else, or (b) is rewritten so it needs
no bound — well-founded recursion on the measure the bound encodes
(`height s1 + height s2`, decreasing at every call by the AVL
invariants the port already cites), which the kernel checks and no
caller has to choose. (b) is preferred where the termination proof is
straightforward (it removes the value rather than parameterising it);
`lfp` (the OCaml may loop) must be (a).

## 3. Target structure

ONE fuel, a parameter of the interpreter, reaching every fuel'd
function through the backend's existing reader lifting (the mechanism
that already threads `tagDefs`, `declare {lean} reader val`):

- The fuel wrapper of a fuel-declared `f` no longer applies a numeral.
  `f` becomes a reader of the ambient fuel: every consumer of `f`
  passes the ambient fuel it itself received, exactly as reader-lifted
  values propagate today; each call of `f` starts its structural
  recursion from the full ambient fuel (as it starts from
  `lemDefaultFuel` now). Sufficient-fuel behaviour is unchanged by
  construction: for every program and every `fuel ≥` the depth the
  program needs at every fuel'd point, the result equals today's.
- The entry points take the fuel explicitly: cerberus `drive fuel …`,
  `runND fuel …`. The binary exposes `--fuel N` (default `10^8`, the
  ONLY place such a numeral may live — a harness choice, overridable).
- DELETED: `lemDefaultFuel`; the per-declaration budget-literal form
  (it mints magic — the defect itself); `CerbFuel.driverFuel`,
  `CerbND.ndDefaultFuel` and the nine fixed-budget `rfl` wrappers.
  KEPT: the sentinel form ``declare {lean} fuel val f = `payload` ``,
  `fuelExhausted`/`fuelExhaustedWith`, `CerbFuel.fuelExhaustedLoc`
  (the outcome atom) and `CerbND.fuelExhaustedKill`.
- Theorems about the semantics quantify over the fuel (`∀ fuel, …`);
  the ∀-fuel exemplar (`test/Unit/FuelExemplar.lean`, symbolic round
  lemmas) is the pattern; the old "wrapper is rfl-defeq to the worker
  at the default" unit gates are restated as "every fuel'd entry is
  fuel-parametric".
- GATE (plant-tested): no fuel numeral in LemLib, generated code or a
  hand-written seam; the grep's only allowed hit is the CLI default.

## 4. Design questions the lem half must settle (in the record, with the reasons)

1. Mechanism: fuel as a NEW reader-lifted ambient ("the backend treats
   fuel like a `declare {lean} reader val` whose type is `Nat`") vs
   folding it into the existing reader parameter record. Prefer the
   one that keeps generated code obviously right and the OCaml output
   untouched (fuel declares are Lean-only already).
2. Hand-written target_reps that call `_lemFuel` workers
   (`CerbMem.lean` ~12 sites) receive the fuel how? Natural answer:
   the memory model's ambient record (already threaded) carries it;
   state the convention so the seam edit is mechanical.
3. What a fuel'd function called from a NON-fuel'd context (no ambient
   fuel in scope) does — there must be none on the execution path
   (the totality gate's slice); outside it, the caller supplies fuel
   explicitly; no default anywhere.
4. Perf: an extra `Nat` argument on every fuel'd call — measure on the
   differential lanes' wall-clock (profile before optimizing); the
   reader lifting already pays this shape.
5. Each LemLib bounded recursion: (b) well-founded recursion on its
   measure, or (a) the ambient fuel — decided per function with the
   reason; `lfp` is (a). Kernel-checked equality theorems between the
   old fuel'd definitions and the new ones where the rewrite is not
   obviously the same function (the F7 pattern, `LemLibTheorems.lean`).

## 5. Aims and constraints (lem-lean, standing)

(1) minimal blast radius for non-Lean lem users — OCaml output
byte-identical (gate); (2) obviously right output; (3) clean design;
(4) reviewable by the upstream lem team. Zero Lean-vs-OCaml
behavioural discrepancies is the standing rule; fuel exhaustion is the
accepted resource exception ONLY because the fuel is now the caller's.

## 6. Sequencing

lem half now (parallel with cerberus Z2); consumer review; lem merge
(ff-only, operator sign-off) → pin bump → cerberus half after Z2 lands
(shared `CerbMem.lean` hunks), before Z3/Z4 so the VALIDATION rewrite
describes the final fuel story. Full differential battery at
`--fuel 100000000`: zero movement expected; the two csmith rows that
exhaust today (`sia_csmith_477/769`) re-run at a larger fuel as the
design's own test.

## 7. Provenance

[USER 2026-09-03]: the ruling (§1). [AGENT] (orchestrator): the
measurement (§2), the target structure, the design questions, the
sequencing. Nothing merged or pushed.

## R1 (2026-09-04) — what changed from the draft, and the consumer input

Revision by the lem-lean worker [AGENT] after the consumer requirements
arrived (refined-cerberus, `refined-cerberus/docs/2026-09-03_request-lem-lean-pmap-laws-and-fuel-scheme.md`,
relayed by the orchestrator) and three further rulings. The record of
what was built is `2026-09-04_fuel-parameter-record.md`; this section
only states the deltas against §3–§5 above.

1. **Mechanism (§4.1 settled): the ambient fuel is a LemLib CLASS, not a
   reader-style explicit binder.** `class LemFuel where fuel : Nat`;
   every fuel'd function and every definition that (transitively)
   reaches one takes an instance-implicit `[LemFuel]` binder (the
   reader-lifting fixpoint decides WHICH definitions — that part of §3
   stands); call sites are textually unchanged (instance resolution
   passes the binder), bare/HOF references need no repair; the wrapper is
   `def f [LemFuel] : T := f_lemFuel LemFuel.fuel`; the entry point is
   `@f ⟨n⟩ …` or `letI : LemFuel := ⟨n⟩`; theorems quantify `∀ [LemFuel]`
   or over `n` via `⟨n⟩` (`@f ⟨n⟩ = f_lemFuel n` by rfl). This is the
   consumer's first requirement ("a single parameter — module-level or a
   typeclass-style instance argument — not per-signature threading");
   the draft's explicit `(fuel : Nat)` binder threaded at every call site
   was built first and rejected (reasons in the record §2). OCaml output
   is byte-identical either way (measured).
2. **A worker takes `[LemFuel]` only if it passes the ambient on** (a
   fuel'd callee, a fuel_consumer, a fuel-lifted def outside its own
   `let rec` block — all-or-none per block, like the counter); a leaf
   worker's only fuel is its counter, so leaf theorems carry no instance.
   Every fuel'd callee starts from the FULL ambient, never from the
   caller's remaining counter (§3's "each call of f starts its structural
   recursion from the full ambient fuel" — kept, and pinned:
   `TestFuelParamCheck` (5)).
3. **New declare `declare {lean} fuel_consumer val f`** for a hand-written
   Lean rep that reads `LemFuel.fuel`: its callers are fuel-lifted; call
   sites unchanged. This is §4.2's answer for the cerberus seams
   (`CerbMem` consumers declare it beside `reader_consumer`; the
   implementation adds `[LemFuel]` and replaces `lemDefaultFuel` by
   `LemFuel.fuel` — mechanical). The draft's alternative ("the memory
   model's ambient record carries it") was rejected: it makes two fuels.
4. **Exhaustion lemmas are generated** (consumer requirement 2):
   `theorem f_lemFuel_zero … : f_lemFuel 0 … = <sentinel> := rfl` for
   every fuel'd function whose parameters are variables/wildcards (lem's
   pattern compiler makes them so; the "not generated" comment path is a
   backstop). Fuel MONOTONICITY is NOT generated: it is not a property of
   the scheme but of how each body consumes exhaustion (a body may absorb
   a sub-call's sentinel and change value at a larger fuel), and with the
   panic payload `fuelExhausted x` — opaque — "≠ payload" is not even
   statable. What it requires is stated in the record §5.
5. **LemLib (§4.5) under the third-form ruling** ([USER 2026-09-03] "my aim
   here is to forbid values that limit the semantics or limit the ways the
   customer can reason about the semantics"): structural recursion on a
   DATA MEASURE (the AVL height stored in a node, an element count, the
   finite square of a relation's endpoints) is admissible — nothing is
   chosen, nothing bounds the semantics, a proof unfolds it. So the
   height-fuelled `unionGo/interGo/diffGo/subsetGo/mergeGo` and the
   count-fuelled `compareAux/equalAux` STAY in that form (documented as
   such), `Pset.join`/`Pmap.join` MOVE from well-founded recursion to it
   (kernel computability for the consumer's closed-term `rfl`s, request
   §2; `join_eq` against the old definition), `Pset.tc`'s
   `(2|r|)^2 + 1` is classified a data measure (the closure lives in the
   finite square of r's endpoints — flagged for the operator: the
   alternative, a caller-fuelled `tc`, was built and withdrawn), and
   `lfpGo` is the caller-fuelled primitive. `lemDefaultFuel` is deleted.
   `lemLeastFixedPoint`'s silent `| 0 => x` is lem's own
   `Set.leastFixedPoint` (set.lem:709) — kept, flagged for the operator.
6. **Deleted forms**: the numeric budget `declare {lean} fuel val f = N`
   (refused with its reason), `lemDefaultFuel`, the `lemDefaultFuel`
   reserved-name guard (the name is ordinary again; `LemFuel` joins
   `lean_constants`).
7. **Fail-closed scope**: a fuel-lifted definition referenced with no
   `[LemFuel]` in scope (lem `assert`, indreln rule, instance method) is a
   generation-time error naming the site; a LIBRARY assert renders as a
   removed-comment (the library's auxiliary files are never built).
8. **Gate** (§3's last bullet): `tests/comprehensive/check_no_fuel_numerals.sh`
   (suite phase `lean-no-fuel-numerals`; comments stripped; four shapes;
   plant-tested). The CLI default named in §3 is the cerberus half's.

### Consumer assessment (relayed by the operator; verbatim)

> Refinement 1: it is broader than the driver. I measured the pinned
> port. The generated tree seals at least six fuelled recursions behind
> fixed wrappers: the scheduler loop, the single-thread loop, the exit
> routine, a printing helper, and the nondeterminism monad's own bind.
> And there are two constants, not one. The driver family uses 10^8,
> while LemLib's default of 10^6 sits behind the expression-step
> recursions. Our own adequacy exports already carry hypotheses bounding
> an expression's potential by that second constant, so we have baked
> the same defect into 60 sites of our statements. The request should be
> about the port's fuel discipline as a whole, not about drive.
>
> Refinement 2: classify it as an interface defect, not a mirror
> discrepancy. The cerberus-lean team's standing rule is zero execution
> discrepancies against the OCaml oracle. On that axis, fuel is
> invisible: OCaml diverges where Lean exhausts, and nothing observable
> differs below the bound. The defect is in the port's interface for
> reasoning, which is a different category under their rules. Framing it
> that way avoids a pointless argument about whether Lean "computes what
> OCaml computes", and puts it where it belongs, in the lem-lean
> backend's fuel scheme.

Both are how the arc is scoped (the orchestrator's response is in
cerberus-lean `lean_frontend/docs/2026-09-03_fuel-parameter-consumer-assessment.md`);
the six sealed recursions are named, with their new shape, in the
record's cerberus dry-run section, and the restatement of a
`potential e ≤ lemDefaultFuel` hypothesis is given there for the
cerberus change manifest.

## R2 (2026-09-04) — the structural declare, D4, monotonicity assessed

Revision by the lem-lean worker [AGENT] after the consumer's review
(refined-cerberus `docs/2026-09-04_review-of-fuel-parameter-design.md`:
ACCEPT; requirement §2 — every fuel'd function on the execution path is
(A) structural on its data, (B) absorbing typed exhaustion, or (C)
unreachable) and the orchestrator's response (cerberus-lean
`lean_frontend/docs/2026-09-04_fuel-parameter-consumer-review-response.md`
§3–§4), adopted by the operator ([USER 2026-09-04] "go ahead with the
merges as proposed, then work on this as you suggest"). Record:
`2026-09-04_structural-declare-record.md`. Deltas against R1:

1. **Form (A) has its declare: `declare {lean} structural val f`.** An
   ordinary `def` with `termination_by structural <param>`; the parameter
   is designated by a syntactic analysis mirroring Lean's checker; the
   well-founded fallback is FORBIDDEN (it would trade kernel
   computability for a `def` keyword silently — the consumer's `join`
   finding); refusal at generation where no parameter works, the Lean
   build as the backstop. R1 §5's "three admissible forms" now read: (a)
   the `[LemFuel]` ambient for (B)-shaped partial recursion, (c) the
   structural declare (or a data-measure index) for (A). D2 (fuel'd
   equalities as instance methods) is resolved by it — a structural def
   can be an instance method — but the three cerberus equalities recurse
   through `List.all (uncurry …) (zip …)`/`listEqualBy`, a higher-order
   self-use no structural checker eliminates: the cerberus half rewrites
   each list traversal as an explicit sibling (the refusal names the site).
2. **D4 = WRAP** ([USER 2026-09-04]): the Lean reps of the `int32`/`int64`
   conversions are the modular `Int32.ofInt`/`Int32.ofNat` (lem's own
   `word_of_int`/`n2w`); `f_int32_overflow` is a registered OCaml-target
   deviation; `2026-09-03_exception-case-rulings.md` D4 addendum.
3. **Monotonicity (R1 item 4, TODO row 13) assessed L on both routes;**
   a hand-proved Route-B exemplar over the generated `spin_lemFuel`
   (`lean-test/TestFuelMonoExemplar.lean`, axioms `[propext]`) fixes the
   statement shape a generator would have to produce; the generation
   itself and its vocabulary are for the operator (record §5).
4. **The (A) census for the cerberus half** (record §6): every one of the
   67 sentinel fuel declares tried as `structural` in a scratch copy,
   mechanically, with the generation-time verdicts and the Lean 4.32.2
   build verdicts.
