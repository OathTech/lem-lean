# Failure translation contracts — proposed revision

[AGENT 2026-10-18] This appendix is a proposed response to review `9a9b409` of
`a331435`. It is an implementation contract, not an implemented backend. The
detailed contracts remain proposed design choices. References below use backend
base `b25be8b` and Cerberus `049eb9a0a` unless stated.

[USER 2026-10-18] The deliverable may include a detailed contract appendix alongside
the short design note. This scope approval does not settle the open design choices.

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
3. Solve effects over the resulting IR and imported contracts; add reader/fuel
   contexts and supply state; emit staged definitions and certificates. Existing
   backend scans supply dependency/traversal infrastructure, not the new effect
   solver. Reader/supply analyses must consume the preserved IR too.

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

The effect solver still determines which *computations* may be reordered or
erased and which primitive calls need error propagation. Judgments are
`Γ ⊢ expression : T ! e`. Literals/variables/lambda construction have effect 0;
a lambda's body is separately checked and translated. Failure has effect F.
Let joins RHS/body effects. Match joins its scrutinee and possible arms, while
emission evaluates only the selected arm. Application joins operand evaluation
effects with the invoked stage's effect; unknown function values have F.
Constructors join field-expression effects; stored callback invocation is F,
not an effect of merely constructing the data. Recursive SCC constraints are
monotone over `{0,F}`; initialize known bodies at 0, unknown calls at F, and
iterate to closure. Computations with effect 0 enter `C` through `.ok`.

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

Top-level nonfunction computations use explicit environments, in source order:

```text
structure A.Env where answer : Nat
def A.init : C A.Env := do
  let _ ← checked' 0                 -- unused source binding still executes
  pure ⟨7⟩
structure B.Env where exported : Nat
def B.init (a : A.Env) : C B.Env := pure ⟨a.answer + 1⟩
def programInit : C (A.Env × B.Env) := do
  a ← A.init
  b ← B.init a
  pure (a,b)
```

Failure in A prevents B initialization and any export access. The generated
entrypoint initializes each dependency once and passes its environment handle;
imports provide types/initializers, not eager global executable values. Exported
functions receive the environment plus their existing explicit/implicit reader
and fuel binders, in their existing order. No hidden context is created.
Retain the existing refusal of supply-drawing top-level values; initially refuse
reader/fuel-dependent top-level values as well. Function declarations with
context parameters are allowed because initialization does not execute their
bodies. Cyclic value initialization refuses.

## 6. Proof interfaces and claim preservation

Reference modules are `Reference.M`, with every definition and target-rep
dependency qualified into the reference package. Executable modules are
`Exec.M`; correspondence modules import both. Reference generation uses the
preserved original typed tree and legacy logical definitions; its `lemSeq` is
inlined as the second thunk. Reference modules have no executable targets or
new native implementations, and neither package imports the other. Shared
total scalar helpers are permitted; accidental cross-package calls are not.

Retain the accepted one-way success relation, with explicit related inputs.
For bases use equality; for products/positive data use matching constructors
and related fields. Use step-indexed relations for callback-bearing recursive
data: index zero is unconstrained, and observing an arrow or forcing ND consumes
an index. For an arrow at index `k+1`:

```text
R(A→B,k+1) f f' :=
  ∀ x x', R(A,k) x x' → ∀ y', f' x' = .ok y' → R(B,k) (f x) y'
```

An exported certificate quantifies over all indices and related arguments.
An `.ok` closure alone is insufficient: its returned value must satisfy this
arrow relation for subsequent invocations. ND's relation quantifies over related
states and successful forcing, relates the action/state pair, and relates every
suspended continuation at the smaller index. The runner consequence is:

```text
NDRel∞ m m' → StateRel∞ s s' → runAll d (.ok m') s' = .ok os' →
  ListRel OutcomeRel∞ (Reference.runAll d m s) os'
```

Here `R∞` means all indices, not just the runner's depth budget. Trace,
multiplicity and list order are included in `OutcomeRel`. This neither
proves absence of new failures nor relates an error to the old logical default.
Failure/order correspondence remains differential evidence until separately
formalized. Do not use a vacuous success premise to transfer total adequacy.

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

Migration order: signatures/primitive replacements → generated type and twin
packages → ND/state/runner API and certificates → measure carriers → caesium
program/theorems and SL no-abort adequacy → executable pins and boundary removal.
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
The controlled run used 30,000,000 checks and six alternating pairs per mode;
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
| 6 | §5 supplies staged zero/wrapper and initialization equations, with explicit initial refusals for unsupported combinations. |
| 7 | Prior comparison withdrawn; generated C confirms matching list lookup/indirect application in both loops. Controlled measurements and noise ranges are recorded above; whole-Cerberus cost remains unmeasured. |
| 8 | Inherited quotation location reported above; no consumer edit or reproduced wording. |

This is not a claim of independent re-review or implementation correctness.
