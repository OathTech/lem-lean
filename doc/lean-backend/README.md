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
  both the OCaml and the Lean code; they share semantics by
  construction. (The heavyweight evidence that this holds in practice
  lives downstream: the cerberus-lean project runs its generated-Lean
  semantics differentially against the OCaml implementation across
  thousands-of-programs corpora — see that repository's
  `lean_frontend/PROOF.md` and `DESIGN.md`.)
- **No `sorry`, no `unsafe`, fail-closed generation.** The backend
  never emits `sorry` or unsafe casts. Where it cannot do something
  soundly — derive an `Inhabited` instance, derive a comparison for a
  function-carrying type — it fails **at generation time** with an
  error naming the type and the escape hatches, or emits a loud,
  greppable runtime failure (`failwithI`), never a silent default.
- **Totality on demand.** By default, recursive Lem functions emit as
  Lean `partial def` (executable, but opaque to the kernel). Marking
  a function `declare {lean} fuel val f = `N`` emits a total
  fuel-indexed worker plus a wrapper at a default fuel — fully
  kernel-transparent. Consumers that need a total surface (cerberus's
  execution slice) apply fuel declares and enforce totality with
  their own build gates.
- **One axiom at the effect boundary.** Lem permits effectful
  target-representation functions (mutable counters, global state)
  behind pure types; Lean's compiler optimizes on purity, so these
  are emitted behind `BaseIO` externs crossed by a single library
  axiom, `LemLib.runEffectful`. That is the one axiom consumers of
  generated code carry; everything else in a downstream proof's
  axiom set comes from Lean itself.
- **Derived instances are real and OCaml-compatible.** `BEq`/`Ord`
  are derived structurally per mutual block with OCaml polymorphic
  compare parity; `Inhabited` is derived fail-closed (bounded,
  per-constructor); instance priorities come from one normative
  table so resolution is deliberate, not declaration-order luck.

## How you check it

- `cd tests/comprehensive && make lean` — generation over the test
  corpus, compilation of everything generated against LemLib, a
  pinned panic-path check (failure sites must raise loudly, never
  degrade to silent defaults), and a negative suite (programs the
  backend must *reject*, rejected for the declared reason).
- `cd lean-lib && lake build` — the runtime plus `LemLibTest.lean`
  (property tests for the set/map layers, including adversarial-key
  comparator coherence).
- Downstream, cerberus-lean's differential lanes are this backend's
  largest consumer test.

## Status

The backend compiles the full Cerberus C semantics (its flagship
consumer) plus the comprehensive suite. Registered residuals, tracked
in the dated records: emission uses a single module-scoped mutable
state (`St` in `src/lean_backend.ml`) with per-lifetime reset hooks —
effect-free emission is a registered future refactor; the Ott grammar
in `language/lem.ott` carries the new declare forms, with
machine-checking pending Ott tooling. Upstreaming intent: every
extension is written to be plausibly acceptable to rems-project/lem
(no fork-only hacks in the core).

Pointers: [DESIGN.md](DESIGN.md) for how it works;
[`doc/notes/`](../notes/) for dated design records;
`src/lean_backend.ml` for the backend itself; `lean-lib/` for the
runtime; bug reports with reproducers live downstream in
cerberus-lean's `lean_frontend/lembugs/`.
