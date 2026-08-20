# Arc-8 lem-backend design: derived Inhabited instances (S1) + failwithI threading (S2)

Date: 2026-08-20. Author: arc-8 S0 worker (probe results in cerberus-lean
`lean_frontend/docs/2026-08-20_arc8-s0-probe-census.md` — the census this
note is derived from; read it first). Charter: cerberus-lean
`lean_frontend/docs/2026-08-20_arc8-daemon-charter.md`. This note
specifies WHAT the two backend passes must produce; it is the S1/S2
work order, grounded exclusively in cerberus-scale measurements (the
April lesson: lem-suite green is never evidence).

## Revocation of the April requirement (authorization)

[USER 2026-08-20] Per the arc-8 charter ("Authorization context"), the
operator authorized revisiting and REVOKING the April-2026 design
requirement `doc/notes/2026-04-09_inhabited_design.md` line 8 — "Does
not require `[Inhabited a]` typeclass constraints". That file now
carries the revocation marker pointing here. Basis: the requirement was
a constraint on the *April fallback design* (blanket constraints on
instance headers in an all-partial-def world), not a discovered
impossibility; the S0 probe re-ran the April experiment at cerberus
scale and the failure mode did not reproduce (census, legs (a)–(c)).

## Two probe facts every design choice below rests on

1. **Lean ≥4.32 partial-def inhabitation is witness-based.** The
   checker (verbatim strategies in the census) accepts a `partial def`
   if (i) some parameter matches the return type, or (ii) Inhabited/
   Nonempty synthesis succeeds *with every parameter turned into a
   local Inhabited instance*, or (iii) unfolding works. Consequence:
   the 318 residual partial defs create almost NO instance demand —
   full tree-wide ablation of all 55 DAEMON fallback instances
   surfaced exactly 8 partial defs (all h-shaped monadic fold/map/try
   combinators) + 31 failwithI/default value-level sites, resolved by
   12 in-module real instances for 11 types, converging green in 5
   rounds, never touching a signature.
2. **Instance-implicit binders propagate for free at concrete call
   sites.** Adding `[Inhabited a]` to a generated def requires NO
   call-site edits and, in today's corpus, no caller-signature edits
   either (measured depth ≤ 1 — every caller of every probed def is at
   a concrete type with a real instance).

## S1 — derived real Inhabited instances

For every generated type the Lean backend currently covers with the
`(priority := low) … default := DAEMON` fallback, instead derive:

1. **Tier 1 (exists today, unchanged):** nullary constructor → 
   unconditional `instance : Inhabited T where default := Ctor`.
2. **Tier 2 (new — replaces DAEMON):** for each constructor whose
   field types are all *derivably inhabitable* (recursively: ground
   types with known instances; `List`/`Option`/`Fmap`/function types
   with inhabitable codomain; type parameters — which induce a
   `[Inhabited tv]` bound), emit a bounded instance
   `instance {tvs} [Inhabited tv_used …] : Inhabited (T tvs)` using
   that constructor with `default`/`[]`/`none`/`fun _ => default`
   fields. **Emit one instance per usable constructor**, priority-
   ordered (first = default priority, rest `(priority := low)`), the
   LemLib `Sum` inl/inr pair precedent (lean-lib/LemLib.lean:90–91).
   WHY per-constructor: the census's `except_foldlM` needs the
   `Result`-side `[Inhabited a]` instance while `trysM` needs the
   `Exception`-side `[Inhabited msg]` one — a single-choice derivation
   leaves a residue; the pair covers both via the checker's
   strategy-2 local instances.
3. **Placement is SAME-MODULE, immediately after the type** (where the
   fallback sits today). Non-negotiable: the census shows the demand
   repeatedly arises in the defining module itself (msum/pick;
   except_foldlM; string0; step_ctx/action_request2) where no
   extra_import eviction can reach.
4. **Recursion/mutual blocks:** a constructor whose field is another
   type in the same mutual block (or the type itself) is usable only
   via the existing tier-1 mutual `default_inhabited` machinery; for
   tier 2 the derivation simply skips self/mutual-referential
   constructors (the census shows 2-level bottom-out — ndM via
   nd_action via kill_reason — is reached by ordinary per-type
   derivation, since kill_reason's `Undef0` is ground). No
   safe_indirect-style global analysis is needed: cross-type
   dependencies resolve through the emitted instances themselves.
5. **Fail-closed (charter durability req 2):** if NO constructor is
   usable, emit NO instance and NO fallback of any kind. If the
   backend itself then generates a demand it knows about (its own
   partial-def emission, a failwithI site, an instance body), raise a
   GENERATION-TIME ERROR naming the type and the escape hatches
   (`declare {lean} skip_instances` + hand target_rep instance).
   Demands the backend cannot see (downstream Lean code) surface as
   ordinary Lean "failed to synthesize" errors naming the type —
   visible, never a hidden inconsistency. NOTE the census's measured
   corpus demand: only 11 of the 55 fallback-carrying types are ever
   actually demanded (ndM, nd_action, kill_reason, exceptM, parserM,
   errorM, t0 (Undefined), expression/expression_ (AilSyntax),
   action_request2, generic_file) + the 6 Core generic AST types probed
   in leg (c); the other fallbacks are dead weight today. All 17 have
   working derivations under rules 1–2 (probe-verified bodies in the
   census).
6. **Deriving-chain hygiene (April class 2):** derived Inhabited
   instances are self-contained `instance … where default := …`
   declarations; they place NO constraints on BEq/Ord/SetType
   instances and none of the probe rounds showed any interaction with
   the sorried BEq/Ord fallbacks or `deriving BEq, Ord` clauses. The
   S1 comprehensive test must still mirror
   `tests/comprehensive/test_parameterized_instances.lem`'s shapes
   (downstream `deriving BEq, Ord` over containers of bounded-instance
   types) — expected to PASS with real instances.

## S2 — failwith → failwithI + selective signature threading

1. **Emission:** every remaining legacy `failwith` call site becomes
   `failwithI` (LemLib.lean:133; identical panic behavior, opaque,
   axiom-free). The existing ground/failwithI classification
   (src/lean_backend.ml:1873–1894) stays; what changes is the
   TYVAR-site handling — instead of falling back to legacy failwith,
   thread a binder:
2. **Threading pass (reader-lift template, lean_backend.ml:105–200):**
   for each def whose failwithI site type contains free tyvars in a
   position NOT discharged by an unconditional instance, add
   `[Inhabited tv]` instance-implicit binders to the def's signature
   for exactly those tyvars, then propagate: any caller that passes its
   OWN free tyvar into that position inherits the binder (monotone
   fixpoint over the call graph). Instance-implicit binders need zero
   call-site rewrites (probe fact 2) — the pass only edits signatures.
   Corpus expectation from the census: the fixpoint closes at depth 1
   — the S2 worklist is 16 defs (census "Class T": nd_mem,
   warns_if_no_active_ex; is_affection, is_concrete_ival,
   impl_isWellAligned_ptrval, impl_memcpy; insupported; illTypedAil;
   ensure_not_c_variable; fromLeft, fromRight, fromJust, foldl2;
   current_scope_is; runStateM_errors, track_temporary_objects) with
   all callers concrete. ~36 further legacy defs (census "Class M")
   need NO binder — their site types discharge against S1 instances
   (msum/pick/exceptM-headed/List/Fmap heads). The pass must compute
   this itself (site-type analysis against the instance set it just
   derived), not hardcode the list.
3. **Instance-method guard:** measured zero failwith sites inside
   generated instance bodies; keep the reader-lift fail-closed guard
   (lean_backend.ml:1109 precedent): a tyvar failwithI site inside an
   instance method (where binders cannot be added) is a
   generation-time error naming the instance and the escape hatches.
4. **Function-field guard:** a def that gained binders and is then
   emitted in a point-free/field position with the bound tyvar
   undetermined will fail Lean elaboration (unresolved instance
   metavariable) — fail-closed by construction; measured zero
   occurrences in today's corpus. No extra machinery unless a negative
   probe shows lem can emit that shape; add a tests/comprehensive
   negative probe for it (durability req 1: shapes not in today's
   corpus).
5. **Prop-instantiation note:** generated polymorphic defs can be used
   with tyvars at `Prop` (measured: nd_mem in Cmm_op's monTrace
   inductive); Lean core's `Inhabited Prop` discharges this — no
   special-casing, recorded so nobody "fixes" it.
6. **fuelExhaustedWith/ground machinery unchanged.** The witness-based
   sentinels never demanded anything in any probe round; the S2 pass
   coexists with them.

## What S3 then deletes

With S1+S2 landed and regenerated: zero references to DAEMON remain in
generated code (the census's two entry-vector classes — LemLib.failwith
through 7 polymorphic functions, and instInhabitedAction_request2 — are
both covered: the first by S2 threading + S1 instances, the second by
S1 same-module derivation, probe round 4). Then LemLib deletes DAEMON,
DAEMON1, DAEMON_impl, DAEMON1_impl and legacy `failwith` (or `failwith`
is redefined ground-only); cerberus re-pins and the absence gate lands
(charter S3). Behavior neutrality: failwithI panics byte-identically to
failwith; derived defaults occupy only unreachable/panic positions —
the S3 differential surface must show zero movement.

## Validation obligations for S1/S2 (from the standing rules)

- Every lem checkpoint pairs with full cerberus regeneration + capped
  build (no lem-only green claims).
- tests/comprehensive: new tests for (i) per-constructor bounded
  derivation incl. the except_foldlM/trysM two-constructor shape,
  (ii) parameterized-instance + deriving BEq/Ord chains (April class
  2, expected PASS), (iii) negative probes: underivable type +
  demanded instance → generation-time error naming type + escape
  hatches; tyvar failwithI inside an instance method → generation-time
  error; shapes beyond today's corpus (durability req 1).
- The S0 census's Class-T/Class-M partition is the cross-check for the
  threading pass output: S2's computed binder set on today's corpus
  must equal Class T (16 defs, exact names above); any difference is a
  finding to resolve before S3.
