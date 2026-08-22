# The synthesized-name (reserved-binder) contract (arc-14 re-mark, be:S2)

Date: 2026-08-22. Status: normative for the Lean backend's synthesized
binders. Enforcement: the generation-time reserved_binder_check in
src/lean_backend.ml (located, fail-closed) + the negative probes
tests/comprehensive/negative/neg_fuel_shadow.lem /
neg_reader_shadow.lem; the none-binder class is separately pinned
POSITIVE (the avoid machinery renames it —
tests/comprehensive/test_name_capture.lem + TestNameCaptureCheck.lean).

## Reserved (user parameters may not use these; checked)

| name | synthesized by | shadow failure mode (pre-check, measured) |
|------|----------------|-------------------------------------------|
| `lemFuel` | fuel'd workers (`declare {lean} fuel val`) | the worker matched the USER's binder: `shadow_probe 0 3` returned the 999 sentinel (probe 2026-08-22) |
| `_lemReader_*` (prefix) | reader lifting / reader_seed injection | the injected leading parameter is shadowed by the user's |

Checked for every fuel'd, seed-marked, or reader-lifted def's clause
parameters (Pattern_syntax.pat_vars_src over the clause patterns).

## Registered residuals (documented, not yet checked)

- Binders introduced by matches INSIDE a fuel'd/lifted BODY are not yet
  scanned (a body-level `lemFuel` binder would shadow at self-call
  rewrites within that arm); price S, mover: an exp-walk collecting
  bound names.
- Worker-name collisions (`<f>_lemFuel` vs an existing def of that
  name) and the derived-code-internal families (`x<n>`, `cmpx_`/`cmpy_`,
  `<T>.beq_derived`, `<T>.<kind>_deriv_aux<n>`, `default_inhabited`,
  `ctor_rank_ocaml`) — internal to generated modules, no user-binder
  interaction surface; loud Lean duplicate-definition errors if ever
  wrong.

## Not reserved (defended differently)

Constructor-named binders (`none`, `some`, `true`, `false`, …): lem's
avoid machinery RENAMES them (`none` → `none1`) in both pattern and
body — probe-measured correct; pinned as a build-failing regression
guard (TestNameCaptureCheck).
