# Lean backend — backlog register

Registered follow-ups for the Lean backend, each with its source and a
price (S/M/L, the sizing used by the dated records). This file is the
one place such items live; the dated records under this directory
carry the reasoning, this file carries the list. Remove an item in the
commit that discharges it, citing the record.

Created 2026-09-02 (docs release-hygiene sweep, item B9 — the repo had
no register; items below were scattered across records). Provenance:
[AGENT] unless marked.

| # | Item | Source | Price |
|---|------|--------|-------|
| 1 | **Run-loop rendering of monadic list combinators for function-typed monads.** Generate `mapM`/`sequence`/`foldrM` over a function-typed monad as a loop inside the monad's `run` function rather than a per-element closure application, so deep element lists stop paying a Lean runtime frame per element (the cerberus `char g[8000000]` front-end hang: the `.lem`-side accumulate-and-reverse fix was built, measured — moved the onset from <8 M to 10 M — and reverted as poor ROI for a trust-surface change). Lean-emission-only (class 0: no OCaml text moves); needs its own ruling before dispatch. | cerberus-lean `lean_frontend/TODO.md` (C9 entry, "FALLBACK CANDIDATE for the next lem arc"), `lean_frontend/docs/2026-09-02_mem-scale-record.md` §S1', `2026-09-01_mem-scale-design.md` C9 row | M |
| 2 | **Refuse a target representation spelled `sorry`.** `src/lean_backend.ml` (the `Backend (_, i) when Ident.to_string i = "sorry"` case, ~:4044-4050) actively special-cases and type-ascribes a user-written `sorry` rep as `(sorry : T)`, while the file header (~:84) says the sorry-emission paths are gone. Under the fail-closed doctrine this is either a declared boundary (register + fix the header) or a hole (error on it, naming `failwithI`/a real rep as the migration). One live consumer use exists (cerberus `frontend/concurrency/cmm_csem.lem` `observable_filter`, registered there as a temporal boundary with the concurrency arc as mover). | quality review m6 (`2026-08-31_backend-quality-review.md`); cerberus-lean `docs/2026-08-20_arc10-s0-triage.md` row 19, `docs/2026-08-20_arc8-results.md` register. [AGENT] the brief for this sweep attributes the item to a "fuel-arc rider"; that phrasing was not located in the records — the cites given are the ones found. | S |
| 3 | **`ground_rep` has no dedicated test or negative probe.** Only the library's single `fromJust` use (`library/maybe_extra.lem:21`) exercises it, indirectly. Add a `tests/comprehensive` positive case (ground vs non-ground call sites, the type ascription) and a probe for the supply-drawing-arguments guard (`src/lean_backend.ml` ~:3790). | quality review "Top 3 coverage gaps" (1) and m5 | S |
| 4 | **m9 library-name entanglement: migrate to library-side declares.** The backend hardcodes Lem-library names — `compare_method_names = ["setElemCompare"; "mapKeyCompare"]`, the `Eq0`/`SetType` extra constraints, the `either`/`vector` builtin-inhabited entries, the `list`/`maybe`/`either` comparison-shape heads, `lean_global_names = ["max"; "min"; "compare"]`, and the source-path library-module test in `backend_common.ml`. Individually defensible (the library is fixed), collectively the largest upstreamability friction after the contextual-keyword fix. Direction: express each as a declare carried by the library `.lem` files (the way `target_rep`/`ground_rep` already are), leaving the backend generic. | quality review m9 | M |
| 5 | **Ott regeneration residual.** `language/lem.ott` carries the new declare forms (fuel sentinel + budget, reader, reader_seed, reader_consumer, supply, ground_rep, skip_instances, extra_import, effectful), but the derived artifacts (the grammar PDF, any Ott-generated checks) have not been regenerated — machine-checking pending Ott tooling in the build environment. | `README.md` §Status; quality review m5 "(+ registered ott-regeneration residual)" | S |
| 6 | **Effect-free emission refactor.** All mutable emission state lives in the single `St` module of `src/lean_backend.ml`, fields classified by lifetime with explicit reset hooks; the planned end state is threading that state through the emitter instead of a module-scoped mutable. Companion (quality review m4): `Backend_common.on_cr_simple_applied` is a process-global `ref` callback installed at every `lean_defs` entry and never uninstalled, and `St.current_module_name` is a pre-call side channel from `process_file.ml` — both should ride the `Backend.Make`/`A` signature. | `README.md` §Status ("effect-free emission is a planned refactor"), `DESIGN.md` "Backend state lives in one module"; quality review m4 | M |

| 7 | **Quadratic library functions (performance only, no behavioural divergence).** `List.genlist` on the OCaml target is the lem definition `snoc (f n') (genlist f n')` (library/list.lem:590-591, quadratic; the Lean rep `List.map f (List.range n)` is linear — a 300 000-element `genlist` did not finish in 10 s on OCaml in the noodle bisect); `Sorting.sort` was `insertSortBy (<=)` on Lean (quadratic) until the parity-fix slice made it `sortByOrd compare` like OCaml. Remaining: give OCaml `genlist` a `List.init` rep (upstream lem, non-Lean change — needs its own nonlean-regress rebaseline). Neither is used by cerberus. | noodle record F9 (`2026-09-03_noodle-backend.md`); parity-fix record | S |

Smaller notes carried from the quality review, not yet actioned (all
S): m3 un-gated shared-path edits (`target_binding.ml` suffix
fallback, `typed_ast_syntax.ml` class-path entities, `output.ml` UTF-8
decode, `target_trans.ml` `add_avoid_type` fail-open `None`); m8
`process_file.ml` shells out `mkdir -p` with an ignored exit; m10
LemLib residuals (three live `partial def`s in the shipped library,
`int32Asr`/`int64Asr` positive-branch shift on the unnormalised value,
`setSigmaBy` ignoring its comparator, dead `listGet?`/`listGet!`
duplicates, duplicate `lemStringFromNatHelper`, division-by-zero
totalising to 0 vs OCaml's raise — one in-code class note wanted);
generated-output cosmetics (double spaces, `(({ ... } : T))`); the
possibly-dead multi-clause equation-compiler render path
(`is_lean_pat_direct` rejects toplevel `P_const`) — probe, then keep a
test on it or delete it.
