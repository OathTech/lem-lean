## Lean 4

The command line option `-lean` instructs Lem to generate Lean 4 output. A module with name `Mymodule` generates a file `Mymodule.lean` and an auxiliary file `Mymodule_auxiliary.lean` (see *Auxiliary Files*). In `declare` forms the target is named `lean`: the standard target-representation declarations are written `declare lean target_rep ...`, and the Lean-specific annotations described in this chapter are written `declare {lean} ...`. Every Lean-specific annotation is target-scoped: it changes nothing in the output of any other backend (see *What other targets can rely on*).

The design intent, in one sentence: the Lean output is meant to be an **obviously right** rendering of the Lem model — the same model that generates the OCaml implementation — with no `sorry`, no `unsafe` casts, no axioms, and a **fail-closed** generator that rejects at generation time anything it cannot translate soundly, naming the escape hatch. Where a runtime failure is the honest translation (a `failwith`, an incomplete match, exhausted fuel), the failure is loud and greppable, never a silent default.

### Compilation

Lem-generated Lean code depends on a Lem-specific Lean library found in the `lean-lib/` directory. This library (`LemLib`) provides the definitions used by the generated output: the `LemOrdering` three-way comparison type, comparator-keyed set and finite-map operations, numeric and string bridges, the loud-failure primitives (`failwithI`, `fuelExhausted`) and the supply-threading split (`supplySplit`). Running `make lean-libs` in Lem's main directory generates Lean versions of the Lem library files into the `lean-lib/LemLib/` subdirectory. The generated library modules live under the `LemLib` namespace (e.g. `LemLib.Bool`, `LemLib.Pervasives`), and imports in generated code use this qualified form.

To compile the generated code, set up a [Lake](https://lean-lang.org/lean4/doc/setup.html) project that depends on `LemLib`. A minimal `lakefile.lean` looks like:

    import Lake
    open Lake DSL

    package MyProject where
      version := v!"0.1.0"

    require LemLib from "path/to/lem/lean-lib"

    @[default_target]
    lean_lib MyLib where
      roots := #[`MyModule]

Then run `lake build` to compile. The library pins its toolchain in `lean-lib/lean-toolchain` (Lean 4.28.0 at the time of writing); the same generated code is also built by its largest consumer on Lean 4.32.2. Always build generated code against the `LemLib` from the same checkout as the `lem` that generated it — the two evolve together.

### What the Lean target emits

Each Lem source becomes one Lean module. Definitions of user modules are emitted at top level; the Lem library modules are wrapped in `Lem_`-prefixed namespaces (`LemLib.Set` becomes `namespace Lem_Set`) so they stay clear of Lean's own names.

- Datatypes become `inductive` declarations, records become `structure ... where`. After each `inductive` the constructors are brought into scope with `export TypeName (Ctor1 Ctor2 ...)`. Mutually recursive types are wrapped in `mutual`/`end`; a mutual block whose members have *different* numbers of type parameters is emitted as indexed families (the parameters become indices) in `Type 1`, since a uniform universe is required.
- Functions become `def`; recursive functions become `partial def` unless a totality declaration applies (see *Recursive Definitions and Totality*).
- Type classes become `class`, instances become `instance` with an explicit priority (see *Comparison Instances*); class methods are brought into scope with `open ClassName`.
- Lean syntax is used natively: `→`, `×`, `∀`, `∃`; record update as `{ r with field := value }`; local names that coincide with Lean keywords are escaped with `«»` guillemets.
- Failure sites — constants whose Lean target representation is `failwith`, and `undefined`-style literals — are emitted as calls to `LemLib.failwithI` (see *Failure Sites*).
- Neither the generated code nor `LemLib` declares an axiom; generated code contains no `sorry` and no `unsafe` (the one user-controlled exception, a target representation literally spelled `sorry`, is listed under *Known Limitations*). Whatever a downstream `#print axioms` reports comes from Lean itself.

### Auxiliary Files

The auxiliary file `Mymodule_auxiliary.lean` imports the main module and carries the executable tests generated from *assertions* in the input. Each `assert name : e` becomes an `#eval` block that checks `(e : Bool)` at build time, printing `PASS: name` on success and throwing `FAIL: name` otherwise — so a false assertion fails `lake build`. Lemmata and theorems are **not** translated: each is emitted as a comment `/- removed theorem name -/`, and no proof obligation is generated for it. The command line option `-auxiliary_level` (`none`, `auto`, `all`) controls how much auxiliary information is emitted, as for the other backends.

### Recursive Definitions and Totality

Recursive function definitions are marked `partial` in the generated Lean output by default, since Lean 4 requires termination proofs for non-partial definitions. This is conservative but correct: the generated code compiles without termination proofs, at the price that a `partial def` is opaque to Lean's kernel (nothing about its body can be proved). There are two ways to opt into totality.

**Structural recursion.** For functions that are structurally recursive, `declare {lean} termination_argument f = automatic` emits a plain `def` and lets Lean's termination checker verify termination; if the checker fails, the Lean build fails.

**Fuel.** For any other recursion the model author can mark the function with a *fuel declaration*:

    declare {lean} fuel val f = `fuelExhausted default_value`

The backend then emits a *total* worker `f_lemFuel (lemFuel : Nat) ...` that recurses structurally on the explicit fuel argument (the self-calls pass the decremented fuel), plus a wrapper `f := f_lemFuel lemDefaultFuel` at the original type. `lemDefaultFuel` is the library default (`10^6` in `LemLib.lean`); it bounds recursion *depth* at the declared points, never value size. When the fuel reaches zero the worker returns the backtick payload, the *sentinel expression*. The convention is `fuelExhausted <witness>`: a loud panic (see *Failure Sites*) that then returns the witness, so an inadequate budget is a visible failure rather than a silent wrong answer.

A **per-declaration budget** replaces `lemDefaultFuel` in one function's wrapper:

    declare {lean} fuel val f = `fuelExhausted default_value`
    declare {lean} fuel val f = 500

The wrapper of `f` then reads `f_lemFuel 500`; every function without a budget declaration keeps `lemDefaultFuel` byte-for-byte. Fuel composes with the reader and supply liftings below (the worker threads the supply through the decremented self-call, and exhaustion returns the sentinel with the supply unconsumed at the cut).

Fail-closed guards (each backed by a probe in `tests/comprehensive/negative/`, named in parentheses): a budget without a sentinel declaration on the same value (`neg_fuel_budget_nosentinel`); a budget that is not a positive integer literal (`neg_fuel_budget_zero`); a budget on a value that carries a Lean target representation, for which no wrapper is ever emitted (`neg_fuel_budget_rep`); a budget on a constant that no function definition defines, which would be silently inert (`neg_fuel_budget_speconly`); fuel on some but not every member of a truly mutual block (`neg_fuel_mutual_partial`); fuel in a mutual block combined with reader lifting (`neg_fuel_mutual_lifted`); fuel combined with `reader_seed` (`neg_fuel_reader_seed`); a user binder named `lemFuel` in a parameter or clause body (`neg_fuel_shadow`, `neg_fuel_shadow_body`); and a user definition named `lemDefaultFuel`, which would silently rebind every wrapper's budget (`neg_default_fuel_name`).

### Inductive Relations

Lem inductive relation definitions are translated to Lean `inductive` types with a `Prop`-valued conclusion. For example, a Lem relation `indreln add : nat -> nat -> nat -> bool` generates `inductive add : Nat → Nat → Nat → Prop where`. Mutually recursive inductive relations (defined with `and`) are wrapped in Lean's `mutual`/`end` blocks. Equality in rule antecedents is rendered as propositional `=`.

### Machine Words and Fixed-Width Integers

Lem's `mword` type (machine words parameterised by bit width) is mapped to Lean's `BitVec` type, with the width computed from the type-level size argument. All standard machine word operations (arithmetic, bitwise, comparison, conversion) have Lean target representations in the library. The `int32` and `int64` types are mapped to distinct newtype wrappers (`LemInt32`, `LemInt64`) around `Int`; note that arithmetic on these wrappers is unbounded `Int` arithmetic — they do not model fixed-width overflow (`LemLib.lean` says so at their definition).

### Comparison Instances

The backend derives `BEq` and `Ord` instances for generated inductive types and records **structurally, per mutual block**, mirroring OCaml's polymorphic `compare` so that the two implementations of one model order values identically: nullary constructors rank below non-nullary ones, constructors within each class are ordered by declaration, and fields are compared left to right. The set/map instance trio the library needs (`SetType`, `Eq0`, `Ord0`) is generated alongside. Types whose constructors carry functions — where OCaml's `compare` raises at run time — get instance bodies that fail loudly through `failwithI` rather than fake comparisons. A mutual block that had to be emitted in `Type 1` (heterogeneous parameter counts) cannot have its comparison instances derived; the backend rejects it at generation time naming the escape hatches (`neg_type1_comparison`).

Every generated or library instance takes its priority from one normative table (`doc/notes/2026-08-22_arc14-instance-priority-lattice.md`): model-provided and derived `BEq`/`Ord` at the default priority, the automatic set/map trio at 500, generic fallbacks low — so a model's own instance beats an automatic one by priority, never by declaration-order accident. A resolution probe in `tests/comprehensive` pins the table.

### Inhabited Instances

Lem programs have failure sites (incomplete matches, `failwith`) whose Lean translation needs an inhabitant of the result type. The backend derives real, bounded `Inhabited` instances for generated types — a nullary constructor when there is one, otherwise a constructor all of whose fields are inhabitable, with `[Inhabited tv]` bounds where a type parameter is consumed — and threads `[Inhabited tv]` binders onto exactly those definitions whose failure sites need them (monotone over the call graph). There is no unsound fallback: if generated code demands an instance that cannot be derived, generation fails with an error naming the type and the escape hatches — `declare {lean} skip_instances type t` plus a hand-written instance, or `declare lean target_rep type t` (`neg_inhabited_underivable`, `neg_inhabited_fn_codomain`). Two further guards: a failure site inside an instance method cannot carry an `[Inhabited]` binder, because instance fields cannot take extra parameters (`neg_failwith_instance_method`); and a failure site in an unconstrained polymorphic `let` has no type to derive an instance at (`neg_failwith_phantom`).

### Failure Sites and the Runtime's Loud-Failure Machinery

`LemLib` declares **zero axioms** (`grep -rn "^axiom " lean-lib/ --include="*.lean"` is empty). Its failure primitives are:

- `failwithI {α} [Inhabited α] (msg : String) : α` — an `opaque` definition whose logical value is `default`, and whose compiled implementation (`@[implemented_by]`) panics with `msg` and then returns `default`. This mirrors OCaml's `raise` at every `failwith`-mapped constant and every `undefined` literal, while keeping library-call semantics (the caller continues with the default) when panics are non-fatal.
- `fuelExhaustedWith (msg) (witness : α) : α` and `fuelExhausted (witness : α) : α` — the same shape for fuel exhaustion; logically the witness, at run time a panic.
- `supplySplit (s : Nat) : Nat × Nat := (s, s + 1)` — a plain definition, the draw primitive of the supply lifting.

These two `opaque`/`implemented_by` pairs (`failwithIImpl`, `fuelExhaustedWithImpl`) are the only ones in the library; nothing else in `LemLib` is `unsafe`. A harness that runs generated code with `LEAN_ABORT_ON_PANIC=1` fail-stops at the first failure site (the `tests/comprehensive` phase `lean-panic` pins both behaviours: message-then-default without the variable, abort with it).

### Target Representations and Ground-Typed Heads

The standard `declare lean target_rep function f ... = ...` and `declare lean target_rep type t = ...` forms map Lem constants and types to hand-written Lean (see the general target-representation documentation in the linking chapter). One Lean-specific refinement exists for polymorphic helpers whose instance should resolve at the call site:

    declare {lean} ground_rep val f = `Ident`

At every application of `f` whose result type is *ground* (contains no free type variables) the backend emits `Ident` in place of `f`, keeps the arguments, and ascribes the result type — `((Ident) arg1 arg2 : T)` — so a type-class instance at `T` resolves exactly there. Applications at non-ground types use `f`'s ordinary representation. The library uses this for `fromJust` (`library/maybe_extra.lem`, mapped to `LemLib.fromJustI1`, a real definition whose success equation holds by `rfl` and whose failure leaf is `failwithI`). A `ground_rep`-mapped call whose arguments draw from a supply is rejected (bind the drawn values in `let`s first).

### Reader Lifting (`reader`, `reader_seed`, `reader_consumer`)

Lem models often read ambient configuration through a nullary constant whose target representation is a global. The reader lifting makes that dependency explicit in the Lean output.

`declare {lean} reader val c` declares `c` a *reader*: every definition that (transitively) reads `c` takes its value as an extra leading parameter, and every call of a lifted definition passes it on. Bare and higher-order references to lifted definitions are repaired by type-preserving partial application over the reader parameters. With several readers the parameters appear in sorted-name order.

`declare {lean} reader_seed val f` marks an *entry point*: `f` itself is not lifted; its first argument supplies the reader value to the lifted definitions its body calls. Guards: exactly one reader must be declared; the seed's first argument must be a simple variable; the seed may not be multi-clause, mutual, inside an instance, or combined with fuel.

`declare {lean} reader_consumer val f` closes the lifting over an extern boundary. A value with a hand-written Lean target representation is opaque to the lifting, so a global its implementation reads would silently escape. Marking it a consumer makes its call sites pass **all** declared reader parameters as extra leading arguments (global sorted order, before `f`'s own arguments), lifts its callers by the ordinary fixpoint, and obliges the hand-written implementation to declare the matching leading parameters. Inside a `reader_seed` definition the seed's first argument is passed instead of the binder. Guards, each with a probe: the value must carry an identifier-form Lean target representation — none (`neg_rc_norep`), a parameter-binding one (`neg_rc_paramrep`) or an infix one (`neg_rc_infixrep`) are rejected; a value may not be both a consumer and a reader, seed, or supply (`neg_rc_mix`, `neg_rc_mix_supply`); a consumer call inside an instance method (`neg_rc_instance`), or anywhere no reader value is in scope — inductive relation rules, lemmas and assertions (`neg_rc_indreln`) — is rejected, as is a consumer used in infix position.

Common to all reader forms: a reader-lifted call inside an instance method is rejected (instance fields cannot take extra parameters); two readers sharing an unqualified name are rejected because their binders would conflate (`neg_reader_dupname`); and the synthesized binder prefix `_lemReader_` is reserved (`neg_reader_shadow`, `neg_reader_shadow_body`).

### Supply Lifting (`supply`)

Lem models also draw from counters — `fresh : unit -> nat` implemented over a mutable cell. A pure-typed but effectful representation is unsound under Lean's optimiser (two calls of a "pure" `fresh ()` may be merged), so the Lean target instead threads the counter as explicit state.

`declare {lean} supply val c` declares `c : unit -> nat` a *supply*: every definition that (transitively) draws from it takes the current supply as an extra explicit parameter (after any reader parameters) and returns the final supply paired with its result. A draw compiles to `let (v, s') := LemLib.supplySplit s`. The transformation A-normalises draw sites in the evaluation order of the OCaml target (the reference semantics of a Lem program): right-to-left within function-application arguments (then the head), tuples, constructor arguments, list literals, infix operands and record fields (in field-declaration order), and as written for `let`/`if`/`match` — so the threaded sequence reproduces the reference counter's dynamic draw order; `&&`, `||` and `-->` keep their short-circuit behaviour (a drawing right operand is placed under the branch, so it draws only when evaluated). The rules are pinned by two-target compiled probes (`tests/comprehensive/parity/`). It is deterministic state-passing only: it emits `let`-bindings, tuples and `supplySplit`, never a nondeterminism constructor. Entry points seed the supply explicitly and receive the final value in the returned pair. With several supplies every lifted definition threads all of them, in sorted-name order.

Because a lifted definition's result type grows a `× Nat`, the repair by partial application that the reader lifting enjoys is unavailable, and the following are generation-time errors: a draw or lifted use under a lambda (`neg_supply_lambda`); a bare, unapplied reference to a lifted definition (`neg_supply_bare`); an application at other than the exact threading arity (`neg_supply_arity`); a lifted constant in infix position (`neg_supply_infix`); a lifted call inside an instance method (`neg_supply_instance`); a draw reachable from an inductive relation rule, lemma or assertion (`neg_supply_indreln`); a supply not of type `unit -> nat` (`neg_supply_type`); a value that is both a supply and a reader or seed (`neg_supply_mix_reader`, `neg_supply_mix_seed`); a supply that is also defined by a live Lem body without a Lean target representation — one constant, two semantics (`neg_supply_defbody`); a truly mutual block of lifted definitions (`neg_supply_mutual`); two supplies sharing an unqualified name (`neg_supply_dupname`); and the reserved binder prefix `_lemSupply` (`neg_supply_shadow`). Definitions carrying a Lean target representation are deliberately not lifted (their bodies are dead text and a hand-written representation cannot take a supply).

### Skipping Instance Generation

The `skip_instances` declaration suppresses all auto-generated typeclass instances for a type:

    declare {lean} skip_instances type my_type

This skips generation of `Inhabited`, `BEq`, `Ord`, `SetType`, `Eq0`, and `Ord0` instances. The user provides these instances in a hand-written Lean file included in their Lake project (imported via `extra_import`, below). This is the escape hatch the generation-time errors above name: use it for types that need hand-written comparisons or a hand-written inhabitant.

### Extra Imports

The `extra_import` declaration injects an import into the generated Lean file:

    declare {lean} extra_import `MyHandwrittenInstances`

This causes the generated `.lean` file to include `import MyHandwrittenInstances` in its import list. Use this when a generated module needs to see typeclass instances (e.g. `BEq`, `Ord`) from a hand-written Lean file. Place the declaration in the consuming `.lem` file, not the file that defines the types, to avoid circular imports. The standard `rename` declaration (`declare {lean} rename ...`) applies to the Lean target as to any other.

### Automatic Renaming

Lean 4 types and values share a single namespace, unlike most other backends. For the Lean target the renaming pass therefore makes constants avoid the names of **all** types in scope — including types imported from other modules, so a cross-module collision (an inductive relation named like an imported type) is renamed rather than shadowed — and adds type-class names to the avoid set as well (other backends never renamed classes, and their behaviour is unchanged). Local names that coincide with Lean keywords are escaped with `«»`.

Some names are reserved by the backend for the code it synthesizes, and a user name that collides with them is a generation-time error rather than a silent rebinding: the binder `lemFuel` and the binder prefixes `_lemReader_` and `_lemSupply`; the definition name `lemDefaultFuel`; and the definition prefix `lemLetRhs_` (used for the single-evaluation representation of destructuring `let`s, `neg_let_rhs_name`).

### Contextual Keywords

The annotation words this backend adds to the grammar — `fuel`, `reader`, `reader_seed`, `reader_consumer`, `supply`, `ground_rep`, `skip_instances`, `extra_import`, `effectful` — are **contextual** keywords: they act as keywords only directly after `declare [targets]`, a position where an identifier can never occur, and remain ordinary identifiers everywhere else, on every target. `let fuel = (1 : nat)` compiles unchanged for `-ocaml` and `-lean` alike. The standing acceptance test is `tests/comprehensive/test_contextual_keywords.lem` (each word as a let-bound name, function name, parameter, pattern variable and record field).

### The Retired `effectful` Annotation

`declare {lean} effectful val f` is retained in the grammar but **refused** by the Lean target with a generation-time error that names the migration path: the supply lifting above. The library no longer contains an effect-projection axiom, and no call-site wrapping is emitted. The probe `neg_effectful_retired` pins the refusal and its message. Hand-written impure externs remain possible on the Lean side, but they are the consumer's responsibility (own `opaque`/`implemented_by` and extraction armour); the backend makes no claim about them.

### Set Comprehensions

Comprehensions whose binders are `IN`-bounded (`{ e | forall (e IN s) | P e }`) are macro-expanded by Lem's front end into comparator-keyed folds and compile like any other code. Forms that survive expansion — the unbounded `{ x | condition }`, and binder shapes the expansion cannot handle — are a generation-time error naming the workarounds: rewrite with explicit library functions, or give the enclosing definition a target representation (`neg_setcomp`). No stub is ever emitted.

### What Other Targets Can Rely On

The Lean backend is a fork-added target and must not disturb the other emitters. Two executable guarantees back that:

- `make nonlean-regress` (repo root) generates the library corpus and every `tests/backends/*.lem` for the nine non-Lean emitters (`ocaml hol isa coq html tex lem ident tex_all`), hashes every artifact and records every exit code, and compares against committed goldens (`tests/nonlean-regress/golden.*`). Any drift — changed bytes, a missing or new artifact, a changed exit code — fails naming the target and file; a run producing implausibly few rows fails too (vacuity guard). Re-baselining is explicit only (`NONLEAN_REGRESS_REBASELINE=1`) and is committed with the change that justifies it.
- The `lean-invariance` phase of `tests/comprehensive` generates each `invariance/inv_*.lem` for `ocaml hol isa coq` with and without its `declare {lean}` lines and requires the outputs to be byte-identical — the `{lean}` annotations are no-ops for every other target.

Together with the contextual-keyword mechanism, this is the upstream-facing contract: adding the Lean target changes no non-Lean output and reserves no identifiers.

### Testing the Backend

`cd tests/comprehensive && make lean` runs, in order: generation of every `test_*.lem` (with an explicit expected-failures list, currently empty); compilation of everything generated against `LemLib` in `lean-test/` (`lake build`, which also executes every `assert` as an elaboration-time check); the compiled behavioural pins — the panic path, single evaluation of destructuring-`let` right-hand sides, integer-division parity with the OCaml library, supply draw sequences, `reader_consumer` injection, and fuel budgets — each a real binary whose output is checked; the negative suite; and the non-Lean invariance phase.

The **negative suite** is the executable specification of the fail-closed guards described in this chapter. Each `tests/comprehensive/negative/neg_*.lem` begins with a header `(* EXPECT: <fragment> *)`; the phase requires the backend to reject the file *and* to mention the declared fragment — a rejection for the wrong reason (a type error, say) is a failure. When a guard in this chapter cites a probe name, that file's `EXPECT` line is the authoritative wording of the error.

The runtime is checked by `cd lean-lib && lake build`, which builds `LemLib` together with `LemLibTest.lean` (kernel-checked equivalence theorems for the finite-map representation and property tests for the set/map layers, including adversarial comparator keys).

### Known Limitations

- **Lemmata and theorems** in Lem sources are dropped (emitted as comments); only assertions become checks.
- **`partial def` by default.** Without a `termination_argument` or fuel declaration a recursive definition is kernel-opaque.
- **Fuel is a depth bound**, not a proof of termination; the default budget is an empirical margin, and exhaustion is loud rather than impossible. A fuel budget on a zero-argument value binding produces a live but vacuous wrapper (semantics preserved).
- **Supply lifting is linear**: no partial application, no lambdas, no instance methods, no inductive-relation rules, no truly mutual blocks (see the guard list). Lifting a monadic region is a model change, not a backend transformation, and is rejected.
- **Supply-lifted top-level value bindings are refused.** The OCaml reference evaluates a value binding once at module initialisation; per-use state passing cannot mirror that, so a drawing value binding is a generation-time error (make it a function of unit).
- **`supply` accepts `unit -> nat` and `unit -> natural`** (both map to `Nat`).
- **Short-circuit operators and the paren-split spine.** `a && (f x)` keeps `&&`'s short-circuit under supply threading, but the eta-expanded spine `((&&) a) (f x)` threads *strictly* (the right operand's draw fires even when `a` is false). This matches the OCaml implementation case for case (OCaml is strict for exactly that shape), and is pinned by `rfl` in `tests/comprehensive/lean-test/TestSupplyCheck.lean`; but the agreement rests on Lem's `Paren` node coinciding with OCaml's full-application detection, and any future normalisation of application spines must re-adjudicate it (in-code notes at the supply transform's general-head branch and at `strip_app_exp`).
- **A target representation spelled `sorry`** is passed through as `(sorry : T)`. This is a user-written escape, not a backend emission — the backend itself never emits `sorry` — but it is a hole in the fail-closed story and is registered for removal (`doc/lean-backend/TODO.md`).
- **`ground_rep`** has no dedicated test beyond the library's `fromJust` (registered in `doc/lean-backend/TODO.md`).
- **Strings are not yet bytes.** Lem `string`/`char` are OCaml bytes but Lean `String`/`Char` (Unicode scalars); non-ASCII bytes diverge (`stringLength`, `toCharList`, `chr`). Design and slice plan: `doc/lean-backend/2026-09-03_string-representation-design.md`; the parity probes `p_str_bytes`/`p_str_escapes` are registered expected failures until it lands.
- **`Debug.print_string`/`print_endline`** print on the OCaml target; pure Lean code cannot, so they fail loudly at runtime (`lemDebugPrintUnsupported`) rather than silently doing nothing as before. A generation-time refusal is the intended end state.
- **`transitiveClosureByEq`** has no Lean rep (nor an OCaml one): unbound for both targets; use `transitiveClosure`.
- **Sets and maps** are `Pset`/`Pmap` (ports of `ocaml-lib/pset.ml`/`pmap.ml`); hand-written Lean that assumed `set 'a = List 'a` must convert (`setToList`/`setFromListBy`).

### Relationship to Coq Backend

The Lean backend is structurally modelled on the Coq backend (the transformation pipeline in `src/target_trans.ml` follows the Coq pipeline). Key differences in the generated output include:

- Lean 4 syntax: `structure`/`where` for records, `inductive` for datatypes, `def` for definitions
- Unicode operators: `→`, `×`, `∀`, `∃` instead of ASCII equivalents
- Native record update syntax: `{ r with field := value }`
- Constructors brought into scope via `export TypeName` after each `inductive` definition
- `Inhabited` instances derived fail-closed for generated types (no axiom-valued inhabitant; underivable-and-demanded is a generation-time error)
- `BEq` and `Ord` derived structurally with OCaml polymorphic-compare parity for every type (nullary constructors below block constructors, whatever the declaration order)
- `LemLib.failwithI` (loud panic, then default) for `failwith`/`undefined` sites instead of Coq's `DAEMON`
- `partial` for recursive definitions by default, overridable with `termination_argument` or a fuel declaration

### Further Reading

`doc/lean-backend/README.md` is the front page for the backend (what you can rely on, how to check it); `doc/lean-backend/DESIGN.md` explains the load-bearing design choices and carries the full declare vocabulary in one table; `doc/lean-backend/TODO.md` is the backlog register. The history of how the backend reached this shape — including mechanisms since retired — lives only in the dated records under `doc/lean-backend/` and `doc/notes/`, not in this chapter.
