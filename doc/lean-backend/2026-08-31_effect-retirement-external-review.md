# Effect retirement: design summary for external review

Audience: the refined-cerberus project (a Lean/iris-lean verifier being
built over the cerberus-lean Core semantics), asked to review this design
as the consumer whose trust story it serves. [USER 2026-08-31]
commissioned this note ("write a note on your proposed design in the lem
repo for the other agent working on refined-cerberus to review").

This is a summary. The governing documents are:

- cerberus-lean `arc/effect-retirement` @ `830fab916`:
  `lean_frontend/docs/2026-08-31_effect-retirement-design.md` (the full
  design note, 2 review rounds: authored, fresh-eyes reviewed
  RATIFY-WITH-AMENDMENTS, amendments applied).
- lem-lean `review/backend-quality` @ `0962814`:
  `doc/lean-backend/2026-08-31_backend-quality-review.md` (the backend
  quality review that shaped the arc's fix-first slice).

## 1. What is being retired, and the contract you get

The Lean port of the Cerberus C semantics (cerberus-lean
`lean_frontend/`) is generated from shared `.lem` sources by this
repository's Lean backend. The port's proof-trust story currently rests
on exactly one axiom: `LemLib.runEffectful : (Unit → BaseIO α) → α`
(`lean-lib/LemLib.lean:54`), the effect-erasure boundary mirroring the
OCaml model's mutable ambient state (fresh-symbol counters, tag-table
writes, debug output). It is declared temporal; this arc deletes it.

**The customer contract (the acceptance criterion, gate-enforced at arc
close):** every constant elaborated from the cerberus-lean repository and
from LemLib has axiom cone ⊆ {`propext`, `Classical.choice`,
`Quot.sound`}. This is the universal form (any definition you unfold, not
just designated entry points), derived from: zero `axiom` declarations
across LemLib + generated + hand-written sources after deletion, plus the
existing bans (no `sorry`, no `native_decide`/`ofReduce*`). Entry-point
`#print axioms` probes (including the `desugar` entry applied at
`Main.lean:512`) remain as end-to-end spot checks.

**What survives, explicitly (ruled [USER 2026-08-31], "axiom gone" bar
with classified survivors):** a small allowlist of kernel-opaque,
pure-signature externs that proofs cannot unfold — they cannot make a
false theorem provable; their hazard is confined to the compiled
evaluator, which sits on the declared differential-validation boundary.
Classification, enforced by the arc's gate ratchet:

| Survivor | Class | Disposition |
|---|---|---|
| `CerberusFresh.digest` (content hashing) | pure-in-fact FFI | becomes a kernel-checked `opaque` (the `with_tagDefs` pattern) in slice C2 |
| `CerbUtils` timing/log refs | no-ops | permanent-declared |
| `CerbGlobal` config refs | should be parameters | temporal; mover = post-arc plumbing slice |
| `CerberusImpl` enum registry | genuinely stateful seam | temporal; mover = the reader/supply machinery this arc builds |

If your proofs need any of these four retired sooner (the enum registry
is the one with real state), say so in review — that re-prioritizes the
follow-up slice.

## 2. The mechanism (ruled decisions)

All decisions below carry operator provenance; the full rulings and their
evidence trail are in the cerberus-side note.

**Q1a [USER]: the split.** The original intent was a purely backend-side
transform. Two independent verifications confirmed that is impossible for
the live `fresh_int` clients: every path crosses a monadic higher-order
boundary (`desugM`/`elabM`), where state-passing is not type-preserving
(the reader transform survives closures via partial application; a supply
threading a result out has no analogous repair), and the constant-
expression leg crosses `Eff.exceptM`, which carries no state component at
all. The ratified design:

- **Backend feature — supply lifting** (`declare {lean} supply val`, this
  repo): the state-passing analog of the existing reader lifting
  (`declare {lean} reader val`), modeled on the same pipeline (declare →
  typecheck field → pre-pass fixpoint → threaded emission), with the
  reader's restrictions carried over as fail-closed generation-time
  guards (no instance methods, no infix position, seed discipline) plus
  supply-specific ones. First-order code threads mechanically.
- **Four bounded model accommodations** (cerberus's `.lem`, not this
  repo): a supply field in the elaboration state + mints, the const-expr
  seam, the `symbol.lem` declare swap, and the `erase_loop_control` local
  state monad. These follow a redirect pattern the fork has executed
  twice before with the oracle byte-identical to upstream.
- Honest cost, ruled with eyes open [USER]: the generated **OCaml text**
  changes (the elaboration-state record is shared between targets; the
  diff is manifest-recorded); oracle dynamic **behavior** is preserved
  and differentially gated (obligations O2/O6). The operator's standing
  objective: "Not disturbing the OCaml *output* is a first class
  objective, not quite a red line but certainly extremely important."

**Q1b [USER]: the one order-moved site.** A review-forced site analysis
classified all 19 live elaboration draw sites: 18 preserve the oracle's
symbol-draw order; one (`with_block_objects`, whose const-alias mints
interleave between its body's construct-time and run-time draws) cannot —
oracle symbol numbering moves on inputs mixing const locals with
drawing statements. Ruled: tolerated, gated by a corpus scan sizing the
affected set first, every affected pinned output enumerated and
rebaselined as an adjudicated instrument change (O6); escalate to a
staged pre-slice if the scan shows nontrivial churn.

**Q2 [USER]: single-stream Lean supply.** Lean-side symbol numbering may
shift; the differential lanes are id-canonicalized by design and the full
battery is the check (O3).

**Q3 [USER]: `reader_consumer` rides the arc** — a small companion
backend feature enabling the tagDefs write-loop closure (the global tag
table and its two remaining write externs are deleted; the table is
passed load→seed directly).

**Debug output** [USER]: leaves the semantics cone entirely — the model
returns values, the driver prints.

## 3. What this repo's arc contains (slice L0 first)

A commissioned quality review of this backend (see the review doc)
mandated a fix-first slice before feature work, and the arc pairs the
supply feature with per-declaration fuel budgets (an independent feature
wanting the same release):

- **L0 (fix first):** contextual-keyword fix (the fork's seven annotation
  words are currently hard lexer keywords — a parser regression for all
  lem users on all targets; any new word this arc adds rides the fixed
  grammar); a nine-target golden-hash regression net for non-Lean output;
  clause-grouping unification; the tuple-destructuring `Let_def`
  RHS-duplication fix (a duplicated supply draw would silently fork
  numbering); `integerDiv` mapping fix (`Int.ediv` → `Int.tdiv`,
  mirroring OCaml `Z.div` truncation); non-ASCII char-literal escapes;
  `setChoose` divergence disposition.
- **L1:** supply lifting + `reader_consumer` + fuel budgets, each with
  fail-closed guards and positive/negative tests in `tests/comprehensive`
  (including compiled-code behavioral tests, closing a known coverage
  gap).
- **C1/C2 (cerberus-side):** adoption, accommodation migration, extern
  deletions, driver seeding; then axiom deletion + gate ratchet
  (census tightening, `runEffectful`-reintroduction ban, plant-tested).
- Close: the two-repo pin dance (lem merges first, ff-only; cerberus
  re-pins and re-gates; both on per-merge operator sign-off).

Blast-radius commitments (operator aims for this repo): minimal impact on
non-Lean lem users (L0's regression net makes this structural; the
review's nine-target sweep is byte-identical today except the keyword
defect being fixed); obviously-right Lean output; clean design;
built for upstream lem review.

## 4. What we ask of the refined-cerberus review

1. **Contract sufficiency:** is the universal axiom-census contract (§1)
   what your adequacy/soundness story needs? Is the three-axiom base
   {propext, Classical.choice, Quot.sound} acceptable to your proofs?
2. **Survivor allowlist:** does any survivor in §1's table sit inside
   definitions you will unfold or need to reason about? (They are opaque
   to the kernel — but if your proof architecture needs, e.g., the
   implementation-defined enum choices as a *function of the impl*, the
   registry's retirement should move up.)
3. **Consumption timing:** the contract lands at arc close (after C2 +
   pin dance). If you need an interim guarantee (e.g. "entry cones only"
   before the universal form), name it.
4. **Anything cerberus-shaped we've missed** from where you sit — the
   operator's standing question is whether generic-looking mechanisms
   carry hidden consumer assumptions.

Review responses: file against this document (this repo, branch
`arc/effect-retirement`) or relay via the operator; the cerberus-side
note is the authoritative technical record and will absorb any resulting
amendments through its established review process.
