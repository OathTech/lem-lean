# Failure-monad initialization: consumer migration notice

Design-stage notice for the implementation and its eventual re-pin. This is
not a report that consumer code has been migrated. The governing scope and
operator ruling are [contract appendix §5](2026-10-18_failure-monad-contracts.md#5-fuel-stages-and-module-initialization).

Inspected sources: cerberus-lean `049eb9a0a16d98df1942fe4dbf86aef9e28978ab`,
cerberus-sl `68832d914227a29c37df381d3e83ad274147e24c`, and cerberus-caesium
`bb751136563ab124fda942d5d44a04ac79ffd653`.

The initialization migration covers `Driver.get_thread_states` and
`Defacto_memory.fresh_allocation_id` / `impl_sequencePoint`. These values become
projections from environments created explicitly at a selected reader/fuel
context. Initialization constructs their ND suspensions; model-state reads,
allocation-counter updates and access-log clearing still happen when forced.
Reader seeding never triggers initialization. Keep initialization context
separate from the ND traversal depth and from a worker's decreasing counter.

Only modules with eligible top-level computations generate initialization
machinery. Unrelated modules and exports acquire no initialization-specific
API changes. Any additional value or interface demand discovered during the
implementation is reported before expanding the migration.

Two SL files need a concrete migration before any re-pin:

| File in cerberus-sl | Current dependency | Required migration |
|---|---|---|
| `CerberusIris/CerberusIris/DriverGlobals.lean` | Direct binds at :92/:97 and elsewhere; `ndRun_get_thread_states` at :154–157 assumes `LemFuel.fuel = m+1`. | Use the initialized projection in the binds. Rewrite it with the supplied same-context equation, retaining the theorem's positive-fuel premise; subsequently migrate the forcing/runner result to the new ND interface. |
| `CerberusIris/CerberusIris/DriverLoop.lean` | The rewrite at :723 uses `@get_thread_states ⟨m+2⟩` in a term exposed after decrement/unfolding. | Use an environment explicitly initialized at that exact context. A different initialization context requires a fresh explicit initialization; do not replace the fuel with an unrelated ambient or remaining budget. |

The implementation supplies an equation for **each** migrated field. In its
initialization-only compatibility stage, where the old types are retained,
the `get_thread_states` equation has this shape:

```text
InitCompat.Driver.init c = .ok env →
  env.get_thread_states = @Reference.Driver.get_thread_states ⟨c.fuel⟩
```

Initialization success facts for the required contexts accompany the equation.
The consumer can rewrite under `ndRun` and apply its old theorem with the same
fuel premise. A consumer is not responsible for reconstructing this bridge.
The equation survives in the proof-only compatibility package after executable
effect lifting. The new executable environment additionally has field
construction equations and old-to-new value correspondence certificates;
the producer also supplies the new forcing equation
`Exec.force env.get_thread_states dr = .ok (.active dr.core_state0.thread_states, dr)`
under the corresponding initialization and positive-fuel hypotheses. This
retains the entire result and state as a consumer rewrite; full runner coverage
and no-abort obligations are separate deliverables.
Equality between old and new ND types is not asserted.

Tracked Lean sources in SL reference none of the two Defacto values; tracked
Lean sources in caesium reference none of these three names. This is a textual
inventory, not a statement that either consumer is unaffected by the broader
failure-monad API/proof migration. Within cerberus-lean, the hand-written call
entrypoint also uses the value (`lean_frontend/CerbCall.lean:277`); its explicit
run setup must supply the initialized handle. No consumer source was edited
for this notice.

Before re-pinning, the implementation updates this notice with actual emitted
names and proved equations, delivers it to the affected consumer maintainers,
and validates the migrated proofs with axiom checks and fresh kernel replay.
Then run the consumer's required build/differential checks at the proposed
pin. No new partial theorem or success-only membership claim may stand in for
the current unconditional claim. Re-pinning, merging and publishing remain
separately authorized actions.
