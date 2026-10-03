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
