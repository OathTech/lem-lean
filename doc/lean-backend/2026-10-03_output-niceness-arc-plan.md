# Output-niceness arc: plan and rulings (2026-10-03)

Branch `arc/output-niceness`, from `mdd/lean-backend` at `6e2526e`.

## 1. Trigger

Feedback from a Lem developer after reading linksem's `src/dwarf.lem` next to
the generated `Dwarf.lean` (relayed by the operator, 2026-10-03, verbatim):

> - the latter has lost a bunch of comments
> - comments added by the translation aren't flagged as such
> - extra blank lines between inductive cases
> - some Lem record types turn into sensible-looking things, but some (eg
>   sdt_subroutine) turn into a Lean inductive with a single constructor that
>   takes a whole mess of positional arguments. On the face of it that looks
>   bad, but I don't know what's idiomatic Lean and what's forced (eg wrt
>   mutual recursive types through records)
> - Claude said "One false start: my first lake build ran under a 20 GB
>   address-space cap and Lean failed to create threads, and a second used a
>   -j flag lake does not take; the third, plain lake build, succeeded." - if
>   building this takes more than 20G, something's suspicious

Operator direction [USER 2026-10-03]: "We should fix these specific things,
then do a general 'niceness' pass intended to make the output nice and
reasonable", and later in the same session: "we should probably rationalize
docs and make sure we have a clean todo list. And I think there are some
lem-upstream findings in documented in linksem / cerberus - we should lift
these to lem using cerberus's 'tray' style".

## 2. Measurements (2026-10-03, lem `6e2526e`; [AGENT])

The trees are linksem's 96 model modules and Cerberus's 85 Lean-built `.lem`
files, regenerated with `lem` at `6e2526e`. linksem's checked-in
`lean/generated/` is identical to this regeneration, apart from two stale
`Dump_image*` files.

1. **Comments lost (Lean only).** A scan counted the top-level `(* … *)`
   comments in `dwarf.lem` and searched for each comment's alphanumeric
   text in the output.
   - `Dwarf.lean` is missing 87 of 797 comments.
   - The OCaml backend's `dwarf.ml` is missing 1, a nested comment the scan
     mis-reads.

   Comments are lost at four kinds of site:
   - in front of a removed `val` or `declare`, which is how the module's
     header essay is lost. `Val_spec` prints a fixed `/- removed value
     specification -/` and drops its skips; the Coq backend has the same
     pattern.
   - on record fields;
   - between match arms;
   - after an expression or a match arm.
2. **Backend comments not flagged.** The backend writes 26 `/- Arc-10 S2: … -/`
   blocks into linksem's generated tree, 25 blocks on OCaml
   polymorphic-compare constructor rank, 11 "Backend-derived computable
   structural size" blocks, and `removed …` markers. None of them is marked
   as backend text, and some use internal jargon.
3. **Blank lines between constructors.** The separator printer
   `sep x s = ws s ^ x` prints the source whitespace before each `|`
   (`"\n  "`). The backend then adds its own `"\n"` and `"  | "`. The
   skips hold the comments as well as the whitespace, so S1 fixes this
   finding and finding 1 with one mechanism.
4. **Mutual and recursive records become single-constructor inductives.**
   The reason given at `src/lean_backend.ml` `Te_record` is "Lean 4 mutual
   blocks cannot contain structure definitions". On Lean 4.32.2 that is
   false. A mutual block of two `structure`s, recursive through `Option` and
   `List`, elaborates; `{ s with … }` works; `SSub.rec` is the expected
   nested recursor. So the inductive form is not forced. Consumer exposure:
   - Cerberus's hand-written `CabsImport.lean:661` builds `specifiers.mk …`
     positionally. That also works with a `structure`.
   - The generated accessor names are the names Lean gives structure
     projections.
   - The affected types are Cerberus `statement`/`specifiers` and linksem
     `sdt_subroutine`/`sdt_lexical_block`.
5. **Memory.** `Dwarf.lean` is the largest generated module (5,773 lines).
   It elaborates in 6.3 s with a maximum resident set of 816,284 kB under a
   16G cgroup cap (`/usr/bin/time -v`).
   - The 20 GB failure was an address-space limit. Lean reserves address
     space per thread, so such a limit kills it while its resident memory is
     small; `scripts/capped` documents the same trap.
   - The memory use is not suspicious.

## 3. Rulings

- [USER 2026-10-03] Ordering against the failure-monad translation (TODO 24,
  the side-effect-free output Cerberus asked for): "Niceness first". S1–S3
  land first under a text-only gate. The failure-monad design pass then
  works on readable output.
- [USER 2026-10-03] Tray scope: "All 16, re-verified". Every upstream-Lem
  finding recorded in the Cerberus, linksem and lem-lean docs gets a draft.
  This includes the five that are only on the archive branch
  `archive/linksem-fixes-2026-09-30` and the machine-word findings. Each
  draft's reproducer is run against pristine upstream `3802cb0`. Filing
  stays with the operator.
- [USER 2026-10-03] Tray home: "lem-lean, copies stay". The new tray is
  `doc/upstream-tray/` in lem-lean. The existing Cerberus
  `upstream-tray/lem/01` and linksem `upstream-tray/lem/01` drafts are left
  untouched, so no consumer-repo changes are needed.

## 4. Slices

One coherent commit per slice; every merge into `mdd/lean-backend` is asked
for separately.

| Slice | Content | Gate |
|---|---|---|
| S1 comments + layout | Carry over every source comment (removed `val`/`declare`, record fields, match arms, trailing comments). Fix the constructor blank lines. Give every backend-written comment one recognisable marker and remove the internal jargon. | Comprehensive suite. Non-Lean output byte-identical. The Lean declaration census of Cerberus and linksem unchanged before/after (Cerberus plan P2c-5's exit test). A new comment-coverage check, plant-tested. |
| S2 records | Mutual and recursive records become `structure`s. Stop needless field renames: `forest : list forest` emits `forest0`. | Comprehensive suite. Both consumers build. The Cerberus ladder and the linksem corpus differential. |
| S3 general niceness | Cerberus plan P2c-5 (width-bounded printer, `.lem` line references) and P1d-9 (double spaces, `(({…} : T))`, …). Starts with a written review of the output, whose item list the operator scopes before any code. | As S1. |
| S4 docs + TODO | README and DESIGN describe the backend as it is; history moves to records; TODO.md becomes one clean register. | Review. |
| S5 lem tray | `doc/upstream-tray/` in the Cerberus format (README, INDEX, one draft per finding, verbatim reproducer output). `upstream-pr/*` branches only where a fix exists. | Verbatim outputs. |

Landing: linksem re-pins after each lem merge. The Cerberus re-pin waits for
the lem-pin slot, which the Cerberus next-phase plan §11.5 shares with the SC
track: one pin dance at a time.

## 5. Constraints from the Cerberus worker (relayed by the operator, 2026-10-03)

Relayed verbatim in substance (the operator's message quoting the Cerberus
worker):

- The shared switch and `deps/lem-pinned` stay at `77ad4fa` until the
  Cerberus `_Alignas` and union-twin slices have landed. Those slices
  regenerate Cerberus's trees, and a lem change in the middle of a slice
  would shift the generated code underneath their gates.
- Every lem-side slice runs `make upstream-drift`, which compares the fork's
  non-Lean output against pristine upstream Lem. Keeping it at "no code
  differences, Cerberus's and linksem's OCaml byte-identical" guarantees
  that lem changes do not move Cerberus's oracle.
- The lem mainline already leads the Cerberus pin (the drift harness, the
  Coq rename). This arc adds to that lead, and the next Cerberus re-pin
  picks it all up at once, after both bug fixes land, unless one of this
  arc's changes affects Cerberus sooner.

How this arc complies [AGENT]:
- Every generation uses the worktree's own in-tree `lem`, writing into
  scratch directories. Verified 2026-10-03: `deps/lem-pinned` is at
  `77ad4fa`, and the switch's `lem -v` prints
  `Lem lean-backend-v0.1.0-alpha.1-20-g77ad4fa`.
- The drift check is part of each slice gate. It runs against pristine
  clients: `deps/cerberus-upstream` and linksem's `worktrees/linksem-upstream`.

## 6. Corrections and findings during the arc [AGENT]

- **Tray count.** When the operator was offered the tray scope, the
  orchestrator said "16" findings, five of them archive-only. That was a
  miscount: the surveyed inventory was 15 mainline items, the `§` lexer
  defect and the five archive-only findings. The tray worker also found the
  `output.ml` block-format decode to be a genuine upstream bug, and the
  orchestrator found the comments-before-`and` loss. The tray therefore
  holds 23 drafts, and its INDEX.md carries the arithmetic. The ruling's
  intent was "all, re-verified"; the number put to the operator was wrong.
- **Comments before `and` in recursive function groups (not fixed in S1).**
  The Lean pipeline loses them, as upstream's prover backends do (tray
  draft 23, reproduced on pristine `3802cb0`):
  - Upstream's `Patterns.remove_toplevel_match` regroups the clauses and
    rebuilds the separators. In Cerberus's `cabs_to_ail.lem` the 18 distinct
    separators of one group became 2.
  - An attempt to print the separators' comments therefore printed one
    comment in front of 29 different definitions. It was reverted, failing
    closed: a missing comment, not a misplaced one.
  - A fix in the shared `patterns.ml` would move Coq/HOL/Isabelle output,
    which the drift guarantee above forbids. It is an upstream report; any
    Lean-only fix needs its own decision.

## 7. S1 record: comments and layout (2026-10-03)

**Changes** (`src/lean_backend.ml`; `src/process_file.ml`, Lean branch only):
- Source comments are kept at every position the backend lays out:
  - a removed `val` (its comments in front, then those inside its type);
  - every `declare`;
  - constructors (trailing comments on the line, leading ones on their own
    lines);
  - record fields and the closing `|>`;
  - `and` in type groups;
  - match arms;
  - the leading comments of every expression, which are taken out of its
    skips in `exp`, so no rendering path can drop them.
- Each source comment is emitted once per file. The identity is physical:
  pattern compilation copies a skip list into several arms.
- A comment inside a one-line expression has its line breaks folded to
  spaces. Lean's layout is column-sensitive, and the census build caught a
  `|` arm ended early by a multi-line comment (`Dwarf.lean`).
- Comment text is escaped (`-/`, `/-`) and padded, so it can neither end
  the Lean comment early nor form `/--` or `/-!`.
- Every comment the backend writes starts with `lem: `. The internal
  jargon is gone. The fixed `removed value specification` marker is gone,
  because a `val` has no Lean counterpart.
- `normalize_layout`, applied to every generated file: outside strings and
  comments, it removes trailing spaces and makes each run of blank lines a
  single blank line. That fixes the blank, indented line between
  constructors.
- New gate `lean-comments`: `tests/comprehensive/test_comments.lem` and
  `check_comments.py`. It checks:
  - every comment is present exactly once; the registered loss is tagged
    `KNOWN-LOST` and must stay absent;
  - no code follows a multi-line comment on its last line;
  - no whitespace-only lines and no blank-line runs.

  Plant-tested 2026-10-03 against copies of the generated file: a removed
  comment gives C1, a duplicated one C2, a multi-line inline comment C3,
  a blank-line run C4, and an emitted `KNOWN-LOST` comment C1.

**Measurements** (scratch tools, derived numbers):

| Tree | Missing comments before → after | Duplicated before → after | Code after a multi-line comment before → after |
|---|---|---|---|
| Cerberus (85 `.lem`) | 958/4060 → 64/4060 | 1 → 0 | 7 → 0 |
| linksem (96 `.lem`) | 927/3833 → 47/3833 | 2 → 2 (both pre-existing) | 6 → 0 |

Both generated trees and LemLib's checked-in sources (30 files) are
token-identical to `6e2526e`'s output, modulo comments and whitespace. The
token check normalises whitespace next to brackets. It was plant-tested on
a `Nat`→`Int` change and on a split `:=`.

**Declaration census** (`Census.lean`: every constant of every generated
and hand-written module; name, kind, structural hashes of type and value):
- **linksem:** 11782 constants in 193 modules, before and after identical
  (0 diff lines). Plant: one string literal changed in `Dwarf.lean` moved
  `attribute_encodings`' value hash. After the revert and a rebuild, 0
  diff lines again.
- **Cerberus** (219 modules, built against the LemLib pin `77ad4fa`):
  - The strict census differs in `Cabs` only, in 360 lines. They are
    hygienic auxiliary names of derived instances
    (`…match_on_same_ctor._@.Cabs.…._hyg.N`), plus the values of 120
    `beq_N`/`ord_N` internals that reference them. Their types are
    unchanged.
  - With macro scopes erased from every constant name (`--erase-scopes`),
    before and after are identical: 34229 constants, 0 diff lines.
  - The strict census is deterministic: a second run on the same build
    gives 0 diff lines.
  - Finding: S1 renumbers inaccessible hygienic helpers in `Cabs`. No
    accessible declaration changes.

**Gate on the candidate** (verbatim tails):
```
make exit 0
lemlib exit 0
Build completed successfully (39 jobs).
comprehensive exit 0
=== Generation: 68 passed, 0 failed, 0 skipped ===
=== Comments and layout (gate) ===
  OK: Test_comments.lean: comments preserved, layout sound
Build completed successfully (197 jobs).
parity: 48 probes: 38 OK, 10 XFAIL (registered, Lean side pinned), 0 FAIL
  OK: 308 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F5)
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
upstream-drift: 944 upstream files; 198 differ (list: …/drift3/differences.txt)
library code files (OCaml/HOL/Isabelle/Coq):
  comments/whitespace only  lib/coq/lem_basic_classes_auxiliary.v   [… 32 such rows, no code row]
lean_keyword_probe: 178 core keywords checked
```
Drift notes:
- The pristine clients were `deps/cerberus-upstream` (`b9aeedcb4`) and
  linksem `worktrees/linksem-upstream` (`4464128`).
- `cerberus-ocaml` and `linksem-ocaml` are absent from the differences:
  their output is byte-identical.
- The non-zero exit is the script reporting the fork's known non-code
  library differences (tex/html/lem renderings), the classes accepted when
  the drift check landed (`98b83c5`).
- S1 changes no shared code. The diff is in `lean_backend.ml` and in
  `process_file.ml`'s Lean branch.

**Not fixed in S1:**
- Comments before `and` in recursive function groups (TODO 26).
- The mutual-record comments of `sdt_subroutine`, which are S2's: the
  records move to the fixed `structure` path.
- Cosmetics, which are S3's: double spaces (`|  Red`, `def  f  (x`), a
  leading space on some own-line comments, the blank line after a
  structure's last comment.
- Lem theorems are emitted as `/- lem: theorem NAME not translated -/`.
  The statement is not kept, although the backend README says theorems are
  "emitted as comments". The S3 review settles this.

## 8. S2 record: mutual records as structures (2026-10-03)

**Change** (`src/lean_backend.ml`):
- A record in a mutual block whose members all have the same number of
  type parameters is now a Lean `structure`. Records in other mutual
  blocks are unchanged. Its fields are printed by S1's field printer, so
  field comments are kept.
- Lean generates the field projections. The hand-made accessor `def`s,
  `match self with | .mk _ _ x .. => x`, are gone. The projections have
  the same names.
- Literals, updates and supply threading of these records take the
  ordinary record path, i.e. `{ f := v, … }` and `{ r with f := v }`.
  Before, a literal was a positional `T.mk` and an update was a positional
  `T.mk` restating `(r.field)` for every unchanged field.
- `St.mutual_records`, and with it `mutual_record_path`, now lists only
  records in a block whose members have different numbers of type
  parameters. Such a block is emitted with indices (`type_def_indexed`,
  `Type 1`). A Lean structure cannot have indices, so there the
  single-constructor inductive is forced and keeps its positional B7
  emission.
- The S1 field printer dropped the comments between `=` and `<|`: the
  first field's handling overwrote them. Both record paths now keep them.
  The case is added to `test_comments.lem`.

**Lean facts checked on 4.32.2** (scratch `mix.lean`, `fld.lean`, run 2026-10-03):
- An `inductive` and a `structure` may share a `mutual` block.
- Structural recursion over `.mk` patterns works through `List`/`Option`
  nesting.
- A recursive parametric structure is accepted.
- `{ b with name := "x" }` elaborates to
  `{ name := "x", body := b.body, parent := b.parent }`.

**Withdrawn [AGENT]: "stop needless field renames"** (§4, the S2 row). The
rename is not needless. In a structure, a field's name is in scope in the
types of the later fields, so a field named like a type captures them.
`structure tree where forest : List forest; other : forest` fails with
`type expected, got (forest : List _root_.forest)`. Lem's renaming of
such fields (`forest` → `forest0`) is what keeps the generated structure
well-formed.

**Gate on the S2 candidate** (FAST-GATE: the commit-level gate of the
two-tier rule; the behavioural lanes run at the merge):
- comprehensive suite: `=== Generation: 68 passed, 0 failed, 0 skipped ===`,
  `OK: Test_comments.lean: comments preserved, layout sound`,
  `Build completed successfully (197 jobs).`,
  `parity: 48 probes: 38 OK, 10 XFAIL (registered, Lean side pinned), 0 FAIL`.
  `test_mutual_record_order.lem` now also covers a heterogeneous block;
  its asserts `mro_h_lo`/`mro_h_hi`/`mro_h_upd` print PASS.
- `nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)`.
- Both consumers build: the linksem library, the Cerberus `CerberusLean`
  library against LemLib `77ad4fa`, and the hand-written `CabsImport.lean`
  with its positional `specifiers.mk`.
- **Census against S1** (linksem strict; Cerberus with macro scopes erased):
  - Changes occur only in `Dwarf` (linksem) and in `AilSyntax` and `Cabs`
    (Cerberus).
  - What changed: the accessor `def`s became projections with the same
    names; `T.mk._flat_ctor` is new; the matcher numbering inside
    `lemSize` moved (`T.lemSize.match_1` is new, and
    `T.<first field>.match_1` is gone).
  - What did not change: the types, their constructors and recursors, and
    every definition that builds, reads or updates these records. In
    particular, `AilSyntaxAux`'s text changed (literals in structure
    syntax) while its declarations are identical.
- The last change, the `<|` comments, is comment-only: its output is
  token-identical to the trees the census was built from. The only
  exceptions are Cerberus's `Core_run` `import Operators`, which the
  Makefile strips, and linksem's two stale `Dump_image*` files.
- Comment coverage after S2: Cerberus 62/4060 missing, linksem 42/3833.

## 9. S3 scope (2026-10-03)

**Review.** A fresh reviewer read the generated output as an experienced
Lean user would. Its findings were grouped into four packages. The
orchestrator re-measured the headline numbers:
- 48% (linksem) and 59% (Cerberus) of the generated text sits on lines
  over 200 characters; the longest line is 105,883 characters.
- `Â§` appears in 32 files.
- Cerberus has 1,044 `(priority := 500)` instance headers.

The packages:
- **A, layout engine:** one-line bodies broken into one arm per line at
  the author's indentation; comments that drift past a signature's result
  type.
- **B, printer cleanup:** spacing, parentheses around atoms and doubled
  parentheses, merged `open` lines, merged binders, the garbled `§` in
  comments.
- **C, derived-code compaction:** shorter instance and derived
  boilerplate. It changes declarations.
- **D, names, docs and types:** docstrings, kept abbreviations, fewer
  renamed locals, fewer ascriptions. Consumer-visible.

**Ruling** [USER 2026-10-03], answering "Which packages should the S3
niceness pass include?": "A: Layout engine (Recommended), B: Printer
cleanup (Recommended)". C and D are not in this arc; they stay candidates
for later decisions. Order [AGENT]: B, then A. Gate for both: the
generated declarations are unchanged, as shown by the declaration census
on both consumers; the token check also applies to whitespace-only steps.
