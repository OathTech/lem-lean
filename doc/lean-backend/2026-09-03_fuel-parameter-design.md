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
