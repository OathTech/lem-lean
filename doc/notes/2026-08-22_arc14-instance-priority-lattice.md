# The instance-priority lattice (arc-14 S2 B4, be:G1)

Date: 2026-08-22. Status: NORMATIVE — every generated or library
comparison/equality instance priority is assigned from this table; an
instance at an undocumented priority is a finding. Enforcement:
`tests/comprehensive/instance_priority.lem` (build-failing resolution
probe) + the emission comments in `src/lean_backend.ml` citing this note.

## The table

Lean priorities: `default` = 1000, `low` = 100; numerals are literal.
Higher wins; ties resolve newest-declaration-first (an ORDER accident —
every deliberate tie below is justified; adding a new tie is a finding).

| Slot | Priority | Who lives here |
|------|----------|----------------|
| model/override | 1000 (default) | lem `instance` declarations from the source model (e.g. symbol.lem's name-only `Eq0 identifier`); hand-written override files (e.g. cerberus CerbStepInstances); LemLib's concrete instances for base types; the generic `[Eq0 a] : BEq a` / `[SetType a] : BEq a` bridges (see "deliberate ties") |
| derived BEq/Ord | 1000 (default) | the backend's derived/`deriving`-bridged **BEq/Ord** instances — MUST stay at default: below the default-priority `[Eq0 a] : BEq a` bridge they would be shadowed and the bridge would complete through `isEqual := x == y`, i.e. through THEMSELVES or a fallback (the pre-arc-10 failwithI race) |
| **auto trio** | **500** | the backend's auto **SetType/Eq0/Ord0** trio (deriving-bridge and comparison-derived) — BELOW every model/override instance (they win by PRIORITY, not order — the sem:S2 fix), ABOVE every generic default and fallback |
| generic defaults | 100 (low) | `Basic_classes`: `[BEq a] : Eq0 a`, `[Ord a] : SetType a`, `[Ord0 a] : OrdMaxMin a`; LemLib's low-priority Sum right-inhabitant; residual (failwithI-bodied) trios/instances for underivable types |
| open-tyvar fallback | 50 | the unconstrained fallbacks for parameterized types (reached only when the bounded instance's `[BEq tv]`/`[Ord tv]` bounds cannot be synthesized; failwithI bodies — loud) |

## Deliberate ties (each with its justification)

1. **derived BEq/Ord (1000) vs the generic `[Eq0 a] : BEq a` bridge
   (1000).** Newest-first: the derived instance (declared in the
   generated module, after Basic_classes) wins. Deliberate: the bridge
   exists for types whose ONLY equality is a model Eq0; lowering the
   bridge would break those, raising the derived instances is a no-op
   (they are already default). The residual order-reliance is confined
   to this pair and probed (probe leg 2).
2. **hand-written override files vs generated real instances (both
   1000).** Newest-first: the override file imports the generated module,
   so it is newer and wins — the documented override mechanism
   (cerberus CerbStepInstances/CerbFunMapInstances pattern). Deliberate:
   overrides exist precisely to win; a priority above default
   (e.g. 2000) is the escape hatch if an import-order accident is ever
   observed (none known).

## The invariant

> For every type with both an auto trio and a model/override instance of
> the same class, the model/override instance wins resolution — BY
> PRIORITY (1000 > 500), independent of declaration order. For every
> type with an auto trio and no model instance, the auto trio wins over
> the generic defaults/fallbacks (500 > 100 > 50).

## The probe

`tests/comprehensive/instance_priority.lem` declares a type with derived
instances AND its own `instance (Eq …)` with distinguishable semantics
(first-field-only equality), then asserts through lem `=` that the MODEL
instance decided. If the auto trio ever wins the race again, the assert
fails at Lean build time (the comprehensive suite's assert compilation),
failing `make lean`. A second assert pins the no-model-instance case
(auto trio semantics, not a fallback panic).

## History

Pre-B4, the auto trio was emitted at default priority and the model's
own instance won by ORDER only ("equal priority resolves
newest-declaration-first") — the be:G1 finding: a semantic accident with
a runtime-failwithI (or silently-wrong-comparison) failure mode. The
sem:S2 sibling (cerberus generated Symbol.lean: location-sensitive auto
Eq0 vs name-only model Eq0 for `identifier`) is the concrete instance of
the hazard; B4 makes the intended winner win by construction.
