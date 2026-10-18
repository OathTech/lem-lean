# Failure translation contracts — design for review

[AGENT 2026-10-18] This appendix is a proposed response to review `9a9b409` of
`a331435`. It is an implementation contract, not an implemented backend. The
detailed contracts remain proposals except for the initialization ruling in §5.
References below use backend base `b25be8b` and Cerberus `049eb9a0a` unless stated.

[USER 2026-10-18] The deliverable may include a detailed contract appendix alongside
the short design note. This scope approval does not settle the open design choices.

[AGENT 2026-10-18] Review `f91761f` invalidated the indexed relation in §6.
The replacement uses unindexed arrows and strictly positive inductive data
relations, with explicit generated fuel/supply effects. The initialization
ruling and its requirements are in §5; design acceptance follows fresh review.

## 1. Preserve computations before target rewriting

Insert a Lean-only entry in `main.ml:transform_for_target` before its target
transformation loop (:277–294), not in `process_file.ml:output` (:430).
The latter is too late. Preserve the original typed modules for reference
generation and for the unchanged OCaml pipeline. The executable Lean path is:

1. Resolve imported effect/representation contracts and source application
   stages, then build a typed strict computation IR. Every actual argument,
   scrutinee and record-update base gets an explicit evaluation node. Ordinary
   applications evaluate arguments right-to-left and then their head. Preserve
   parentheses/application groups and source lambda boundaries. Record updates
   evaluate their base once, then replacement fields in reverse declaration order.
2. Lower dictionaries, patterns, comprehensions and representations through this
   IR. Lean inline substitution substitutes **value variables**, never pending
   computations. It may drop or duplicate a variable, but its preceding bind
   remains. Pattern compilation preserves a single scrutinee evaluation and the
   selected arm. Do not run today's raw `inline_exp_macro` or record-update
   macros over unnormalized executable expressions.
3. Resolve reader/fuel/supply demands on the preserved IR, insert typed fuel
   stages (including zero payloads) and explicit supply operations, then solve
   effects over that IR and imported contracts. Any later effect-introducing
   lowering must re-solve before emission. Existing backend scans supply
   dependency/traversal infrastructure, not the new failure-effect solver.

The reusable scans are `lean_fuel_prepass` (:1193), `lean_reader_prepass`
(:1243), and `lean_supply_prepass` (:3538); today's aggregation is
`lean_analysis_prepass_all` (:3727). Move their inputs to the preserved IR
without duplicating their reader names, binder order or existing refusal rules.
Solve mutual groups together: use one canonical signature per member, join
effects to a fixed point, and preserve the declared structural/fuel recursion
scheme. No member gets a different type from caller-specific inference.

For an inline constant function, `constant (checked n)` becomes
`let v ← checked' n; pure 42`, even when `v` is unused. A later optimization may
erase that bind only with a total, effect-free certificate. The witness is
`failure_monad_inline.lem`; it must distinguish current Lean's successful 42
from the oracle failure at zero, and the proposed emission must preserve that
failure.

OCaml has its own target-specific inlines (`target_trans.ml:234`). The reference
schedule for an OCaml inline/representation is its expanded OCaml body, not an
invented strict source-call schedule. Such overrides require a scheduling
contract before Lean normalization; absence is a generation error. Ordinary
calls use the strict rule above. This changes no OCaml output.

The shipped probe source `FailureMonadSpike.lean` makes the repaired shapes
explicit: `branch` binds the checked RHS before selecting the branch;
`closure` binds it before constructing the returned lambda; `discarded` and
`unused` bind computations whose values are ignored (B15/B15b); `unitPattern`
binds before matching unit. `buildClosure` can fail during construction (A3),
and `arguments` selects the right-hand failure first (A4). A failed first bind
absorbs the continuation; the theorem `error_absorbs` pins that law.

After all executable emission uses these binds, remove `lean_backend.ml`'s
`lemSeq` emitter (:7448–7455) and `LemLib.lemSeqImpl`. The reference package
keeps only the legacy logical second-thunk definition, without its native
override. Removal requires the implementation's compiled parity/strictness
checks and kernel correspondence, not this hand-written spike alone. The
existing `failwithIImpl`/fuel overrides remain current boundaries until their
own executable leaves have also become explicit errors; this design adds none.

## 2. Types, effects and boundary declarations

Choose conservative **uniform lifting of function values**, without effect
polymorphism or call-site specialization in the first implementation. This
chooses a stable cross-module representation over selective-lifting complexity;
its whole-program performance cost remains unmeasured:

```text
T ::= a | base | T × T | D T… | T → T
e ::= 0 | F                 0 ≤ F; join = maximum
C A = Except Failure A
V(a)=a'                    V(base)=base
V(D T…)=D' (V T)…           V(A→B)=V A → C(V B)
```

All function-valued fields, arguments, results and instantiated type parameters
use this canonical representation, including pure callbacks. Thus
`apply f x = f x` has type
`(A' → C B') → C (A' → C B')` and value `.ok (fun x => f x)` after its
first argument. A list mixing pure/fallible callbacks has one element type;
the pure lambda is translated recursively, including its nested arguments and
results. There is no attempt to wrap an opaque higher-order function in `.ok`
and pretend its callback types changed. Such functions need a replacement.

The failure solver classifies computations and identifies calls requiring
error propagation. It provides only one input to any future optimization proof;
failure freedom alone never authorizes erasure or reordering. Judgments are
`Γ ⊢ expression : T ! e`. Literals/variables/lambda construction have effect 0;
a lambda's body is separately checked and translated. Failure has effect F.
Let joins RHS/body effects. Match joins its scrutinee and possible arms, while
emission evaluates only the selected arm. Application joins operand evaluation
effects with the invoked stage's effect; unknown function values have F.
Constructors join field-expression effects; stored callback invocation is F,
not an effect of merely constructing the data. Recursive SCC constraints are
monotone over `{0,F}`. Seed every invocation stage with the effect of its
**translated zero payload**, body and callees, then iterate to closure. A
`fuelExhausted` payload contributes F even if the source body only recurses;
a successful value sentinel or typed exhaustion kill contributes 0. A returned
closure contributes 0 now and its body's effect when invoked. Unspecified
native fuel consumers contribute F until their stage contracts prove otherwise.
Computations with effect 0 enter `C` through `.ok`.

Keep the existing reader/supply dependency sets alongside this failure bit.
A `tick` draw has failure bit 0 and a nonempty supply-effect set. Any dependent
caller inherits that set; unsupported supply/HOF forms still refuse. A proposed
no-observable-effect certificate must establish totality at **every allowed
budget**, failure bit 0 after lowering, no supply mutation or diagnostic output,
and unchanged reader/environment dependencies. Unknown dependencies preclude
that certificate. Initially retain every strict computation node: there is no
bind-erasure/reordering optimization to justify with the failure bit alone.
No reader read may move across a context change.

Concrete obligations from `test_fuel_param.lem:42–44` and `test_supply.lem:34`:
`let _ ← loudSpin 0 n; pure 42` is an exhaustion error; from supply `s`,
`tick; tick` returns `(.ok (s+1), s+2)`. With transformer
`Supply → (Except Failure A × Supply)`, `tick; error; tick` returns
`(.error failure, s+1)`: retain the first draw and never perform the last.
`FailureMonadContracts.lean` proves these equations for the proposed emission;
these are specification witnesses, not evidence that a new analyzer exists.

Proposed declaration grammar (new syntax, not accepted by today's parser):

```lem
declare {lean} failure_signature val succ = nat -[0]> nat
declare {lean} failure_rep val succ = `Boundary.succ`
declare {lean} failure_signature val checked = nat -[F]> nat
declare {lean} failure_rep val checked = `Boundary.checked`
declare {lean} failure_signature val map =
  forall 'a 'b. ('a -[F]> 'b) -[0]> (list 'a -[F]> list 'b)
declare {lean} failure_rep val map = `Boundary.map`
declare {lean} failure_signature val start = nat -[F]> (unit -[F]> nat)
declare {lean} failure_rep val start = `Boundary.start`
```

`-[e]>` annotates one invocation stage. `failure_rep` names a Lean value whose
type is obtained by replacing each annotated arrow with `A' → C_e B'`, where
`C_0 B=B` and `C_F B=C B`. Required replacement types are:

```text
succ    : Nat → Nat
checked : Nat → C Nat
map     : (A' → C B') → List A' → C (List B')
start   : Nat → C (Unit → C Nat)
```

The generated public wrappers expose canonical `V` arrows: e.g. `map' f =
.ok (fun xs => Boundary.map f xs)`. The replacement's callback parameters are
already canonical; nested result arrows are recursively adapted at their
declared stages. Pure declarations whose negative-position arrow types are not
canonical are refused, not coerced by assuming callbacks cannot fail.

Contracts include a stage-by-stage evaluation specification: callback order,
conditions, cardinality and returned closures. A name and type alone are
insufficient. A pure implementation must be kernel-total and have a checked
dependency cone without project runtime overrides, hidden failure, partial or
unsafe execution; standard toolchain primitives retain their existing boundary.
Replacements with a source definition additionally require
success correspondence and order/failure witnesses. Unsupported opaque/native
boundaries remain explicit blockers; an annotation is not a purity proof.

Emit a versioned signature artifact per module containing canonical datatype and
dictionary schemas, effects, representations and dependency/source fingerprints.
Separate generation consumes these signatures and rejects mismatches; it never
re-infers an imported type from that invocation's callers. Clone positive
recursive datatypes once per source declaration, not per call. Lem dictionaries
become explicit translated records; their methods follow canonical arrows.
Only certified total methods may provide Lean's Bool-valued `BEq`/`Ord`
interfaces. Dictionaries with fallible comparison require
effect-aware set/map implementations. Type/Prop/measure contexts requiring a
fallible value refuse. Abstract target-represented types require a translated
type and a relation/operations package; otherwise refuse. No new axioms or
runtime overrides are permitted.

## 3. Library scheduling is part of the contract

For `List.map`, use the actual `count_map`/`map_tr` schedule in
`library/list.lem:271–301`, not Lean's ordinary left-to-right monadic map:

```text
mapTr acc f []       = pure (reverse acc)
mapTr acc f (x::xs)  = do y ← f x; mapTr (y::acc) f xs
countMap f [] c      = pure []
countMap f (x::xs) c = do
  ys ← if c < 5000 then countMap f xs (c+1) else mapTr [] f xs
  y ← f x
  pure (y::ys)
map f xs             = countMap f xs 0
```

For lengths at most 5001, callbacks run in reverse element order. For longer
lists, positions 5002 onward run left-to-right first, then positions 5001 down
to 1. Returned values remain in original list order. Distinguishing cases:
failures at 1 and 3 in `[1,2,3]` select 3; failures at 5002 and 5003 in
`[1,…,5003]` select 5002. A reversed adapter fails the latter. The witness
recipe checks callback traces and both failures against compiled OCaml.

Other library replacements need the same source-specific analysis; unknown
fold/set/map/comparison scheduling refuses. Flat recognized Boolean operator
applications short-circuit. Parenthesized partial applications such as
`((&&) a) (checked n)` are strict, as already pinned by
`TestSupplyCheck.lean:61`; classification is by source application shape and
the oracle expansion, not merely the operator name.

## 4. ND, state and runner interfaces

Use `C` for global failure, preserving domain kills as a different constructor.
`Failure` distinguishes model failure (site/message) from budget exhaustion
(site/budget description); preserve the oracle's diagnostic prefixes. Existing
Lem `Exception` results remain data inside `C`: for instance, an explicitly
constructed domain exception becomes `.ok (Exception.Exception e)`, while
`failwith` becomes `.error (.model …)`. Do not conflate an ordinary result
constructor with a raised failure or add an error-swallowing default.
The raw seam interface, before canonical curried wrappers, is:

```text
mutual
  Action' A I E CS S =
    active A | killed (Kill E) | nd I (List (I × ND' A I E CS S)) |
    guard I CS (ND' A I E CS S) |
    branch I CS (ND' A I E CS S) (ND' A I E CS S) |
    step I (List (I × ND' A I E CS S))
  ND' A I E CS S = ND (S → C (Action' A I E CS S × S))

bind : ND' A I E CS S → (A → C (ND' B I E CS S)) → ND' B I E CS S
liftND : (S2 → C S1) → (S2 → C (S1 → C S2)) →
         (I1 → C I2) → (E1 → C E2) →
         ND' A I1 E1 CS S1 → ND' A I2 E2 CS S2
```

`bind m f` constructs a suspension. Forcing it first binds `force m s`; an
active `(v,s1)` next binds `f v`, then forces that action at `s1`. A kill returns
unchanged. Other nodes retain their constructor and recursively bind their
continuations, using the source map/constructor scheduling contract. Fuelled
versions retain the present decremented mutual-worker counter and typed kill
at zero. This raw signature is a seam adapter, not permission to merge failures
into kills.

`force (liftND get put li le m) s2` binds `get s2`, then `force m s1`;
for its result `(act,s1')`, it evaluates the curried `put s2 s1'` computation
before `liftAction li le act` (the source pair's right-to-left order), then
returns the translated action and updated state. Callback applications inside
`liftAction` obey `nondeterminism.lem:254–280`, including `List.map`'s contract.

Runner interfaces distinguish construction failure from forcing failure:

```text
Outcome A E S = Status A E S × List String × S
Frame = nd Nat | step Nat | guard | branch Bool
Abort = { failure : Failure, path : List Frame }
runAll, runFirst : Nat → C (ND' A I E CS S) → S →
                  Except Abort (List (Outcome A E S))
runFirstTrace : (I → C String) → Nat → C (ND' A I E CS S) → S →
                (List String × Except Abort (List (Outcome A E S)))
```

`runAll d cm s` matches `cm`: `.error e` becomes
`.error {failure := e, path := []}`, and `.ok m` calls `runNode d m s`.
Thus even at zero depth a construction error propagates; a successful
suspension is not forced at zero. `runNode (k+1)` binds forcing before examining
the node. NDnd/NDstep
visit siblings **left-to-right**, prepending each completed branch's list to
the accumulator. NDbranch binds the left result, then the right, and finally
concatenates left ++ right. Do not translate the old Lean append expression
using generic right-to-left scheduling: this seam mirrors explicit OCaml binds
in `smt2.ml:75–82,117–132`. `runFirst` preserves the current first-child policy
and its already-declared constraint/randomness deviations. Fuel zero remains
the existing successful singleton exhaustion-kill outcome, after construction
arguments have been evaluated.

First global failure returns `.error` immediately: discard accumulated outcome
lists, do not visit later siblings, and expose no final model state. Thus
`bind (put s1) (fun _ => .error e)` fails on forcing and returns no `s1`.
A construction `.error e` runs no action. Two failing siblings labelled L/R
select L even though successful NDnd result lists are reversed. `Abort.path`
records constructor/child-index frames without needing an `I` renderer;
`runFirstTrace` also retains labels already
emitted before failure. Earlier successful branch results/states are not
silently reclassified as outcomes. External diagnostic IO is outside these
pure signatures: preserve an explicit trace contract or refuse the boundary.
The CLI routes `.error` to its loud model-failure/exhaustion reporting path and
a failing exit, never to an empty successful outcome list. Existing output
prefixes remain part of the differential observation.
Supply remains a separate state transformer `Supply → (C A × Supply)` and
retains its current state on failure; that does not promise a final ND model state.

C-TF1 is a deliberate compatibility exception: preserve `CerbFail.failStopND`
and its seven accepted typed model-stop sites, including
`CerbMem.allocateObject`'s requested-address arm (:2542), as their existing
distinguished kills. Preserve typed fuel outcomes too. Do not classify them as
ordinary UB or claim they implement global OCaml abort. Moving C-TF1 into
global failure would change sibling exploration and requires a separate ruling;
recommend deferring that change and retaining its boundary disclosure.

A small Lean 4.32.2 realization exposed a representation issue: a mutually
recursive ND function field returning nested `Except` failed automatic `SizeOf`
specification generation (and hiding it behind an abbreviation also failed the
kernel's nested-datatype check). The witness uses an explicit mutual result type
with error/ok constructors and a total conversion at the forcing interface;
both conversion round trips are proved. No generation option is disabled.
This is an implementation option for the recursive representation, not a new
observable outcome or runtime override. The full six-constructor, stateful
production representation still needs its own kernel check.

## 5. Fuel stages and module initialization

Do not use `lean_hoist_tail_binders` (:4732) across a computation stage. Example
for a function producing a closure, with lexical reader `r` and an explicitly
declared function-valued zero payload:

```text
mkStage r 0 n       = .ok (fun _ => .error exhausted)
mkStage r (k+1) n   = do
  v ← checkPrefix r n
  pure (fun u => if n=0 then pure v else do
    g ← mkStage r k (n-1)
    g u)
mk [LemFuel] r n    = mkStage r LemFuel.fuel n
mk_zero r n        : mkStage r 0 n = .ok (fun _ => .error exhausted) := rfl
mk_wrapper n r x   : @mk ⟨n⟩ r x = mkStage r n x := rfl
```

The prefix executes when `mk` is applied to `n`; invoking the returned closure
uses its captured remaining counter and reader. It neither reruns the prefix
nor obtains a fresh ambient counter. Unrelated calls still use their ambient
fuel. Zero preserves the *declared stage*: a function-valued sentinel that
fails on invocation must not become an earlier construction error. Raw
sentinels need a typed staged replacement; unknown snippets refuse.

Initially retain current supply/HOF, supply/mutual, supply/measure and
supply/tail-hoisting refusals. Also refuse a measured staged definition whose
measure needs a not-yet-supplied argument. This is an explicit proposed support
limit, not a conflict silently resolved by moving evaluation. Measure hypotheses
remain pure. Supporting the refused forms requires a later design/ruling.

[USER 2026-10-18] The operator authorized initialization under an explicit
context, with a narrowly bounded rollout. The following are requirements:

1. Generate initialization machinery only where a module evaluates a top-level
   nonfunction computation with possible failure or fuel/reader dependence.
   A module with no such computation acquires no initializer or environment;
   the initialization pass preserves its existing API.
2. Supply a kernel-checked projection equation for each migrated value against
   its current per-use definition at the same context. Implementation authors
   deliver those equations and the consumer rewrite path; consumers are not
   asked to invent compatibility proofs themselves.
3. Creating an environment is an explicit operation for a particular context.
   Reader seeding cannot create another one implicitly. A caller changing the
   initialization context must perform initialization explicitly again.
4. The authorized rollout is exactly the three Cerberus values and four positive
   test cases listed below. Additional candidates from the implementation
   census are reported for a new disposition; they do not enlarge this set.

The operator rejected both refusing the existing inputs and continuing
context-sensitive per-use evaluation as a permanent alternative. Before a
consumer re-pin, deliver a migration note naming SL's `DriverGlobals.lean` and
`DriverLoop.lean`; the draft is [beside this appendix](2026-10-18_failure-monad-consumer-migration.md).

Eligibility is a computation-stage property: a function declaration's body is
not run at initialization, and failure only in a stored callback does not make
construction fallible. A nonfunction binding that executes a function-producing
expression is checked at its construction stage. Existing refusals of
supply-drawing top-level values and cyclic value initialization remain. No
source value is converted into a unit function to defer its evaluation.
Within an eligible module, only the affected values enter the environment;
unrelated exports retain their API. Local initializers preserve source order,
including discarded computations and a single RHS for destructuring bindings.

For an eligible module, use this shape (illustrative, not another rollout item):

```text
structure M.Env where value : T
def M.init [LemFuel] [ReaderInstances…] (explicitReaders…) (dependencies…) : C M.Env := do
  value ← initializeValue …
  pure ⟨value⟩
def M.value (env : M.Env) : T := env.value
```

The caller supplies fuel/readers in their existing binder order and initializes
eligible dependencies first, once per program environment. Initialization
failure prevents export access and subsequent initializers. Module definitions
and imports themselves perform no hidden runtime initialization. ND-valued
initializers build suspensions; they do not run model-state operations. An
initialized suspension retains the fuel/readers captured at construction.
Initialization context and an ND runner's depth budget remain separate.

Transport initialized values only through the affected definitions and their
private workers; importing an eligible module is not a reason to add an
environment argument to every export. Keep unrelated exports in that same
module unchanged by this pass too. The live `get_thread_states` uses in Lem
belong to `Driver.driver_globals` and `Driver.drive`; :493 is commented-out
source and is not a dependency. `Mini_pipeline`'s use of `Driver.driver2`
therefore does not, by itself, demand an environment parameter. The explicit
hand-written entrypoints (`Main`/`CerbCall`, including `CerbCall.lean:277`) arrange
initialization and capture the resulting handle for the run. They do not
generate environments of their own. The implementation must not broaden
ineligible-module APIs to make transport convenient: an actual new dependency
requiring that change is a new finding under the fixed rollout rule.

[AGENT 2026-10-18] Separate initialization compatibility from the later effect
representation change. First prove the initialization-only equations while
retaining the old value types; after effect lifting, retain those equations in
the proof-only compatibility package and supply the executable correspondence
beside them. This avoids writing an ill-typed equality between old ND and new
ND types, and does not keep a per-use executable compatibility path.

The required theorem family for **every** migrated field is:

```text
InitCompat.M.v_projection_eq (c) (env) (hinit : InitCompat.M.init c = .ok env) :
  env.v = Reference.M.vAt c
```

`Reference.M.vAt c` is today's definition specialized to the actual instances
and explicit readers in `c`, not an arbitrary new reference value. These are
ordinary equalities, including for function- or ND-valued fields. For each
paired binding emit one RHS initializer and a projection equation for each
name. Dependency environments have matching initialization/equality premises;
prove their compatibility in dependency order. Also supply initialization
success facts for the approved successful contexts, so the equation cannot be
used as a vacuous replacement for a positive test.

Consumers first rewrite `env.v` with that equation at the exact context of the
old use. For example, the initialization-only migration of SL's read theorem is:

```text
ndRun env.get_thread_states dr = (.NDactive dr.core_state0.thread_states, dr) := by
  rw [InitCompat.Driver.get_thread_states_projection_eq c env hinit]
  exact ndRun_get_thread_states (m := m) hm dr
```

Here `hm : c.fuel = m+1`; other readers are those explicitly supplied by `c`.
This delivers the demanded rewrite before changing ND types. A proof about the
old runner is not automatically a proof about the new runner.

For the final executable environment, also ship a same-representation equation
and the old-to-new relation for each value:

```text
Exec.M.init c = .ok env → Exec.M.initField_v c = .ok env.v
InitCompat.M.init c = .ok old → Exec.M.init c = .ok env → R(T) old.v env.v
```

`initField_v` is the construction-stage expression in the preserved IR,
parameterized by the same initialized dependencies and earlier fields as the
module initializer. It is private initialization machinery, not a per-use
export. Only the initializer invokes it at runtime. The proofs live in modules
importing Reference and Exec; executable modules import neither their proofs
nor Reference. The first equality and the compatibility projection equation
remain deliverables; the relation is an additional obligation, not a substitute.
Full runner equations/no-abort claims then migrate as specified in §6.
In particular, deliver the final executable forcing equation for the SL-facing
value, with the same positive-fuel premise as its existing theorem:

```text
Exec.Driver.init c = .ok env → c.fuel = m+1 →
  Exec.force env.get_thread_states dr =
    .ok (.active dr.core_state0.thread_states, dr)
```

This is a producer-supplied rewrite for the new ND interface, in addition to
the required initialization-only projection equality. It preserves the full
forcing result, including state, and does not ask the consumer to derive a
useful equation from a generic success relation. Ship the zero-context typed
kill equation too; never strengthen the positive-fuel hypothesis silently.

| Authorized case | Required migration and retained pin |
|---|---|
| Test 1: `test_fuel_param.lem:64`, `spun_value` | Preserve the source and `TestFuelParamCheck.lean:60–62` results: environments at fuel 100 and 7 project 0 and 999. The latter is a successful declared sentinel. |
| Test 2: `parity/probes/p_fuel.lem:41`, `results` | Keep the parity row and OCaml bytes. The Lean driver initializes explicitly at 200 and 100000, checks success, then prints the existing two blocks without changing the pinned output. |
| Test 3: `test_instance_reader.lem:64`, `sw_plus_one` | At `Sw=5` the projection is 6; migrate both the kernel and compiled reader tests using the supplied equation. |
| Test 4: `test_instance_reader.lem:68`, `(sw_a,sw_b)` | One RHS evaluation; separate projection equations retain 5 and 6 at `Sw=5`, including signature and compiled checks. These four cases occupy three source files. |
| Cerberus `driver.lem:138`, `get_thread_states` | Initialize the suspension at the chosen context. Migrate the direct SL binds and `ndRun_get_thread_states` via its projection equation, then the new ND/runner contracts. |
| Cerberus `defacto_memory.lem:120`, `fresh_allocation_id` | Initialize the suspension; do not draw its model-state allocation counter until forcing. Supply the projection equation even though the external consumers do not reference it. |
| Cerberus `defacto_memory.lem:478`, `impl_sequencePoint` | Initialize the suspension; do not clear the model-state access log until forcing. Supply its projection equation as well. |

The three consumer definitions are confirmed at Cerberus `049eb9a0a` in
`generated/Driver.lean:247` and `Defacto_memory.lean:168,463`. The earlier
nonfunction-header scan was not a complete implementation census; any additional
case discovered later is reported rather than silently migrated or refused.
SL `68832d9` references `get_thread_states` in
`CerberusIris/CerberusIris/DriverGlobals.lean` (including :92, :154–157) and
`DriverLoop.lean:723` (explicit budget `m+2` after unfolding). Retain the precise
context in each rewrite. Executing under a new initialization context requires
explicit initialization even if a proof can show that some values agree.
Equality rewriting is not permission to skip that operation or to trigger it
through seeding or proof simplification. Tracked Lean source searches found no SL references to
the two Defacto values and no references to any of the three in caesium
`bb751136`; the note records these bounded searches and the pre-re-pin obligation.

The prototype proves context-quantified projection equations for its fuel and
reader fields, a consumer rewrite, and preservation of an initialized value
under a new reader seed. It also pins successful and exhausted-value contexts
and a construction error before access. Those examples validate the interface;
the implementation must supply the actual per-value equations listed above.

## 6. Proof interfaces and claim preservation

Reference modules are `Reference.M`, with every definition and target-rep
dependency qualified into the reference package. Executable modules are
`Exec.M`; correspondence modules import both. Reference generation uses the
preserved original typed tree and legacy logical definitions; its `lemSeq` is
inlined as the second thunk. Reference modules have no executable targets or
new native implementations, and neither package imports the other. Shared
total scalar helpers are permitted; accidental cross-package calls are not.

Retain one-way success correspondence, with explicit related inputs, but
**discard the earlier finite-index relation**. Review `f91761f` proves it rejects
`applyZero f = f 0`; quantification over all indices does not repair that error.
Use ordinary, unindexed value relations and a separate computation relation:

```text
CR R v m'       := ∀ v', m' = .ok v' → R v v'
R(base)        := equality
R(A→B) f f'    := ∀ x x', R(A) x x' → CR R(B) (f x) (f' x')
```

Products relate their fields. Generate mutually **inductive** relations for
strictly positive recursive datatypes, with one rule per matching constructor;
expand arrow-field relations into quantifiers when checking positivity.
Recursive relation occurrences may appear in result positions, never in the
antecedent for a callback argument. A function-valued payload uses its complete
ordinary arrow relation, even when stored in recursive data. Accepted source
strict positivity must be rechecked for the translated datatype and generated
relation; an abstract boundary needing some other relation must provide a
kernel-checked package, not an unproved indexed fallback.

For ND, `ActionRel` has one matching-constructor rule per action, and `NDRel`
has the suspension rule below. The mutual recursive occurrences are positive:

```text
(∀ s s', StateRel s s' →
   CR (ActionRel × StateRel) (Reference.force m s) (Exec.force m' s')) →
NDRel m m'
```

These are relations over the actual inductive ND values, including their
function fields; they do not assume a coinductive infinite object. The state
relation is a parameter independent of this mutual block. Reference induction
provides hypotheses for all results of a suspension's function field. An ND
constructor's successors use the same relation, without losing information
about higher-order payloads at an arbitrary index. Generated nested relation
auxiliaries (e.g. lists of continuations) must also pass kernel positivity.

The two composition obligations are ordinary application and bind:

```text
R(A→B) f f' → R(A) x x' → CR R(B) (f x) (f' x')
CR R(A) x m' → (∀ a a', R(A) a a' → CR R(B) (k a) (k' a')) →
  CR R(B) (k x) (m' >>= k')
```

`FailureMonadContracts.lean` proves these, `applyZero`, two consecutive callback
invocations, a returned closure that accepts a callback, and a recursive ND
suspension carrying that closure. It also proves that callbacks returning
0/1 are unrelated. The ND witness has active/next constructors and unit state;
it validates the recursive/higher-order shape, not the full production runner.
The target full-runner theorem, still to be proved, is:

```text
NDRel m m' → StateRel s s' → runAll d (.ok m') s' = .ok os' →
  ListRel OutcomeRel (Reference.runAll d m s) os'
```

Trace, multiplicity and list order belong to `OutcomeRel`. These contracts
neither prove absence of new failures nor relate an error to the old logical
default. Failure/order correspondence remains differential evidence until
separately formalized. Never transfer total adequacy through a vacuous success
premise. Initialization compatibility uses §5's same-context projection
equalities and corresponding initialization hypotheses; old per-use-context
theorems are rewritten with those supplied facts before effect representations
change. Cross-context reuse requires an additional proved equation.

A migrated measure obligation compares complete computations at the relevant
stage, including error and supply state, e.g.

```text
hack_measure_sufficient' (h : IsValuePexpr' p) (hn : size p ≤ n) :
  Exec.hackBodyFuel n ed td ce env mem file csm p =
  Exec.hackBodyFuel (size p) ed td ce env mem file csm p
```

The wrapper uses the RHS; prove the value case returns `.ok cval`, rather than
erasing discarded work by `simp [lemSeq]`. Function-valued results need equality
of the returned functions/computations, not merely equal observed successes.
General monotonicity remains TODO 13.

For caesium `bb751136`, modify `DriverExecution.cycle` to execute the discarded
`step_ctx` filter after the state read. Add an effectful primitive to its program
language/denotation, then prove unconditional **new-to-new** denotation equality
and complete runner equality:

```text
cycleE_denote : denoteE (cycleE k concurrent) = Exec.driver2BodyFuel k …
driver_coverageE : projectRun (runProgramE d (cycleE k concurrent) s) =
                   runAll d (Exec.driver2BodyFuel k …) s
```

`projectRun` maps successful lists and preserves the entire abort. Keeping the
old cycle program unchanged would require proving that discarded computation
cannot fail on every reachable state; it is not justified by the old
`cycle_denote` proof (:120–147). Old theorems remain about the reference model
only until these new unconditional claims are proved.

For cerberus-sl `68832d9`, preserve the strength of `t21_adequacy_concrete` (:46):
under its existing program/library/heap premises, prove for every budget
`∃ os, runAll … = .ok os ∧ ∀ o ∈ os, allowed o`. This includes a new no-global-abort
obligation. Merely quantifying over successful-list membership would weaken the
claim by dropping error executions. If the stronger theorem cannot be proved,
report the claim blocked; do not publish the conditional version as equivalent.

Migration order: census against the fixed initialization scope → contracts and
initialization-only projection equations at legacy types → generated type/twin
packages and executable field certificates → ND/state/runner API and certificates
→ measure carriers → consumer notice, caesium program/theorems and SL no-abort
adequacy → executable pins and boundary removal. The compatibility stage is an
implementation proof dependency, not a request to re-pin consumers to an
intermediate implementation.
Estimate **XL, cross-repository API/proof migration**. The 268 generated sites,
two handwritten references, and 63 declarations/15 carriers are inventories,
not an edit estimate. New function/data relations, ND forcing, runner coverage
and no-abort proofs dominate the unmeasured risk. Kernel replay and axiom checks
remain required for every new certificate.

## 7. Measurement scope and outstanding record integrity

Review finding 7 invalidates the first timing comparison as an isolated cost:
one loop used list lookup/indirect application and the other a direct call.
The revised pair uses the same list-of-functions interface and per-iteration
lookup. Fresh generated C inspection confirms `List.get!Internal` followed by
`lean_apply_1` in both loops (`CurrentMain.c:111–112`, `PrototypeMain.c:115–116`),
not just in the terminal call. The executable recipe prints these sites.
`f_let_unused` was selected because the same discarded check has a successful
positive-input path and a zero-input failure, while its later output exposes
incorrect sequencing. Its last callback is the timed workload; the other
probes cover control shapes without entering the timed loop. Both binaries
receive identical count, seed and terminal-input arguments. The controlled run
used 30,000,000 checks and six alternating pairs per mode;
all exits, checksums and messages passed. Derived summaries (seconds), emitted
by the commands in the short note:

```text
startup current: wall median=0.002835 range=0.002657..0.003974; cpu median=0.000; max_rss_kb=8704
startup prototype: wall median=0.002828 range=0.002680..0.003192; cpu median=0.000; max_rss_kb=8596
startup-failure current: wall median=1.073542 range=1.072178..2.026155; cpu median=0.000; max_rss_kb=8632
startup-failure prototype: wall median=0.003380 range=0.002858..0.004147; cpu median=0.000; max_rss_kb=8588
success current: wall median=2.714583 range=2.698971..2.758259; cpu median=2.705; max_rss_kb=8628
success prototype: wall median=1.792342 range=1.768152..1.830307; cpu median=1.780; max_rss_kb=8732
failure current: wall median=3.819506 range=3.802355..4.407558; cpu median=2.735; max_rss_kb=8620
failure prototype: wall median=1.794701 range=1.765485..1.842109; cpu median=1.785; max_rss_kb=8656
```

Abort latency is noisy, as the zero-work failure range shows; do not attribute
that wall-time difference to propagation checks. Whole-Cerberus cost remains unmeasured.
The implementation charter should measure a fixed bounded driver corpus with
the actual ND runner, callback-bearing data, supply and deep error propagation;
report success and first-abort cases separately. Do not multiply this shallow
microbenchmark by the number of `lemSeq` sites.

Review finding 8: the inherited attributed quotation is in Cerberus
`lean_frontend/VALIDATION.md:292`, R2. Existing quotations also occur beside
`failwithI`/`lemSeq` in `lean-lib/LemLib.lean`. These locations are reported for
the owner; this design pass neither reproduces their wording nor edits them.

| Finding | Disposition in this revision |
|---|---|
| 1 | §1 moves normalization ahead of target macros and preserves strict binds; the compiled inline witness reproduces erasure and the prototype preserves failure. |
| 2 | §2 chooses uniform canonical function values, gives constraints/declarations/types and separate-module contracts. This is a proposed support decision. |
| 3 | §3 specifies the actual threshold-dependent map schedule and strict Boolean partial application; OCaml/prototype traces match at lengths 3, 5001, 5002 and 5003, with the two distinguishing failures. |
| 4 | §4 gives forcing/bind/lift/runner interfaces, state/trace policies and the explicit retained C-TF1 exception. |
| 5 | §6 gives related-input certificates and concrete stronger consumer obligations; no claim is transferred merely by discarding errors. |
| 6 | §5 supplies staged zero/wrapper equations, explicit staged-measure limits and the approved selective initializer contract with mandatory projection equations. |
| 7 | Prior comparison withdrawn; generated C confirms matching list lookup/indirect application in both loops. Controlled measurements and noise ranges are recorded above; whole-Cerberus cost remains unmeasured. |
| 8 | Inherited quotation location reported above; no consumer edit or reproduced wording. |

This is not a claim of independent re-review or implementation correctness.


## 8. Independent review dispositions and bounded proof check

| Finding in `f91761f` | Disposition |
|---|---|
| 1, high | Accept. The old relation is invalid. §6 replaces it; the small application/composition and recursive suspension witnesses are kernel checked. Full generated certificates and runner correspondence remain implementation obligations. |
| 2, medium | Accept. §1/§2 seed translated fuel zero stages before closure, retain supply dependencies and prohibit erasure/reordering based on failure freedom alone. Discarded exhaustion and draw-before-error equations are proved. |
| 3, medium | Accept. §5 records the approved selective initialization policy, fixed migration set, required projection equations and consumer notice. Ineligible-module APIs remain unchanged by initialization; additional transport requirements are new findings, not inferred scope. |

Reproduce the new witnesses independently of the measured spike (from the
worktree root, with the project toolchain available):

```sh
mkdir -p .tmp/failure-monad-contracts
cp lean-lib/lean-toolchain .tmp/failure-monad-contracts/
cp doc/lean-backend/FailureMonadContracts.lean .tmp/failure-monad-contracts/
cat > .tmp/failure-monad-contracts/lakefile.lean <<'EOF'
import Lake
open Lake DSL
package FailureContracts
lean_lib Contracts where
  roots := #[`FailureMonadContracts]
EOF
(cd .tmp/failure-monad-contracts && CERB_MEM_MAX=2G ../../scripts/capped lake build +FailureMonadContracts:olean)
(cd .tmp/failure-monad-contracts && CERB_MEM_MAX=2G ../../scripts/capped lake env leanchecker --fresh FailureMonadContracts)
```

Validation: the new module built successfully without warnings. Derived tally:
23 theorem axiom lists were empty, including four context/projection witnesses
added after the ruling. `leanchecker --fresh FailureMonadContracts` exited 0.
At `50ab017`, review `f91761f`'s original `RelationCounterexample` was also rebuilt:
both theorem axiom lists were empty, and fresh kernel replay exited 0. These
small checks ran sequentially under a 2G cap; no full dependency rebuild was
needed. The measured spike is unchanged; its corrected timings were independently
reproduced in `f91761f`, and are not rerun here. No comprehensive or consumer suite is rerun
for these specification/proof witnesses. No `sorry`, extra axiom, runtime
override, or generation/linter suppression is added.
