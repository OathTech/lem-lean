# The Lean backend for Lem

This fork adds a **Lean 4 backend** to [Lem](https://github.com/rems-project/lem):
`lem -lean` compiles Lem definitions to Lean 4 source that builds
against the [LemLib runtime](../../lean-lib/). It was built to port
the [Cerberus](https://github.com/rems-project/cerberus) C semantics
to Lean — the same Lem model that generates Cerberus's OCaml
implementation now also generates a Lean implementation — but it is a
general Lem backend, exercised by its own test suite independently of
Cerberus.

**Provenance.** The Lean backend was developed primarily by AI agents
(Claude, Anthropic) operating under the direction and review of a
human operator (Mike Dodds). Upstream Lem is by its own authors (see
the [top-level README](../../README.md)); the dated design records in
[`doc/notes/`](../notes/) are the working history of the backend.

Who this is for:

- You have a Lem specification and want an **executable Lean 4
  version** of it.
- You want the generated code to be **reasoned about in Lean** —
  the backend's design choices (below) exist to keep generated code
  proof-friendly.
- You want to understand **how the backend works** — see
  [DESIGN.md](DESIGN.md).

## Quickstart

```bash
# Build the lem binary (repo root; needs OCaml + opam deps, see the
# top-level README's install section)
make

# Compile a Lem file to Lean
cat > demo.lem <<'EOF'
open import Pervasives
let double (x : nat) : nat = x * 2
EOF
./lem -wl ign -i library/pervasives.lem -lean demo.lem
# → Demo.lean + Demo_auxiliary.lean, next to the source, importing LemLib

# Build the runtime the generated code imports
cd lean-lib && lake build
```

A full working setup — generation, compilation against LemLib, and
the negative/panic test legs — is `tests/comprehensive/`:
`cd tests/comprehensive && make lean`.

## What you can rely on about the output

- **One model, two implementations.** The same Lem source generates
  both the OCaml and the Lean code, so any semantic divergence between
  them is a backend bug, not a modelling change. (The heavyweight
  evidence that divergences are absent in practice lives downstream:
  the cerberus-lean project runs its generated-Lean
  semantics differentially against the OCaml implementation across
  thousands-of-programs corpora — see that repository's
  `lean_frontend/VALIDATION.md` for what is compared, against what,
  and what its gates guarantee, and its `lean_frontend/DESIGN.md`.)
- **No `sorry`, no `unsafe`, fail-closed generation.** The backend
  never emits `sorry` or unsafe casts. Where it cannot do something
  soundly — derive an `Inhabited` instance, derive a comparison for a
  function-carrying type — it fails **at generation time** with an
  error naming the type and the escape hatches, or emits a loud,
  greppable runtime failure (`failwithI`), never a silent default.
- **Totality on demand; the fuel is yours.** By default, recursive
  Lem functions emit as Lean `partial def` (executable, but opaque to
  the kernel). A recursion that is structural on its data is marked
  `declare {lean} structural val f` and emits an ordinary `def` with
  `termination_by structural <param>` — Lean proves termination, the
  well-founded fallback is forbidden, and the kernel computes through
  it (`decide`/`rfl` on closed terms). Anything else is marked
  ``declare {lean} fuel val f = `sentinel` ``, which emits a total worker
  that recurses structurally on an
  explicit fuel counter, plus a wrapper `f [LemFuel] := f_lemFuel
  LemFuel.fuel` that starts the counter from the AMBIENT fuel — a
  parameter of the generated code (an instance-implicit `[LemFuel]`
  binder on `f` and on everything that reaches it), never a numeral:
  no default exists in the library or the output; the entry point
  chooses (`@f ⟨n⟩ …`), a theorem quantifies (`∀ [LemFuel]`), and
  `f_lemFuel_zero` states the exhaustion case by `rfl`. The backtick
  payload is the expression returned when the counter runs out; write
  it as `fuelExhausted <witness>` to make exhaustion a loud panic. A
  fuel'd function whose recursion is bounded by its data (but not in the
  structural checker's shape) adds ``declare {lean} fuel_measure val f =
  `List.length xs + 1` ``: the wrapper starts the counter from that
  computable measure of the arguments (`def f (xs : …) := f_lemFuel
  (<measure>) xs`), so `f` is fuel-free for its callers and the kernel
  computes through it; the backend emits the per-function sufficiency
  obligation (`f_measure_sufficient`: worker = wrapper at every fuel at
  or above the measure) whose proof you write in
  `<Module>_lemMeasureProofs.lean` — a missing or mistyped theorem fails
  the build, and a `sorry` fails the suite's token gate.
  Cerberus applies fuel declares across its whole execution path and
  checks that slice is total in its own build.
- **Zero axioms; effects are explicit state.** Neither the library
  nor generated code declares any axiom: everything in a downstream
  proof's axiom set comes from Lean itself. Ambient counters are
  threaded as explicit state ("supply lifting": a definition marked
  ``declare {lean} supply val`` takes and returns the counter; draws
  are `LemLib.supplySplit`, a plain def), and ambient configuration
  is threaded as an explicit parameter ("reader lifting"). An earlier
  design had a library axiom (`declare {lean} effectful`) projecting
  `BaseIO` externs into pure types; it is gone, and the backend now
  rejects that annotation at generation time, naming supply lifting
  as the replacement (the note at the top of `lean-lib/LemLib.lean`
  records the change).
- **Derived instances are real and OCaml-compatible.** `BEq`/`Ord`
  are derived structurally per mutual block with OCaml polymorphic
  compare parity; `Inhabited` is derived fail-closed (bounded,
  per-constructor); instance priorities come from one normative
  table so resolution is deliberate, not declaration-order luck.
- **Unsupported forms are rejected, not approximated.** Set
  comprehensions with `IN`-bounded binders
  (`{ e | forall (e IN s) | P e }`) are macro-expanded to folds and
  compile like any other code; the forms that survive expansion — the
  unbounded `{ x | condition }`, and binder shapes the expansion
  cannot handle — are a generation-time error with rewrite
  suggestions, never a silent stub. The other unsupported corners
  follow the same pattern — see the negative suite in
  `tests/comprehensive/negative/`.

## How you check it

- `cd tests/comprehensive && make lean` — generation over the test
  corpus, compilation of everything generated against LemLib, a
  pinned panic-path check (failure sites must raise loudly, never
  degrade to silent defaults), and a negative suite (programs the
  backend must *reject*, rejected for the declared reason).
- `cd lean-lib && lake build` — the runtime plus `LemLibTest.lean`
  (property tests for the set/map layers, including adversarial-key
  comparator coherence).
- `grep -rn "^axiom " lean-lib/ --include="*.lean"` — zero hits;
  `#print axioms` on any downstream theorem shows what its proof
  actually rests on.
- Downstream, cerberus-lean's differential lanes are this backend's
  largest consumer test.

## Status

The backend compiles the full Cerberus C semantics (its flagship
consumer) plus the comprehensive suite. Known residual work, registered
in [TODO.md](TODO.md): emission uses a single module-scoped mutable
state (`St` in `src/lean_backend.ml`) with per-lifetime reset hooks —
effect-free emission is a planned refactor; the Ott grammar
in `language/lem.ott` carries the new declare forms, with
machine-checking pending Ott tooling. Upstreaming intent: every
extension is written to be plausibly acceptable to rems-project/lem
(no fork-only hacks in the core).

Pointers: [DESIGN.md](DESIGN.md) for how it works;
[TODO.md](TODO.md) for the backlog register (registered follow-ups
with sources and prices); the upstream-facing manual chapter
[`doc/manual/backend_lean.md`](../manual/backend_lean.md);
[`doc/notes/`](../notes/) for dated design records;
`src/lean_backend.ml` for the backend itself; `lean-lib/` for the
runtime. Defects in this backend are recorded here, as dated records
in `doc/lean-backend/` with reproducers in `tests/comprehensive/`;
reports we intend for upstream Lem itself are drafted downstream in
cerberus-lean's `lean_frontend/docs/upstream-tray/lem/` (see that
directory's README).
