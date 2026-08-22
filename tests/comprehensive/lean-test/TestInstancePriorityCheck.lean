/- Arc-14 S2 B4 (be:G1 + sem:S2): the instance-priority resolution probe.
   Normative lattice: doc/notes/2026-08-22_arc14-instance-priority-
   lattice.md; type shapes: tests/comprehensive/test_instance_priority.lem.

   Each #guard asks LEAN's instance resolution (not lem's static
   elaboration, which inlines class methods at known types) which
   instance wins, and fails the BUILD (`make lean` -> lean-compile) if
   the winner is wrong. #guard is evaluator-checked — a TEST, exactly
   what a resolution probe needs (never described as kernel-checked). -/
import Test_instance_priority
open Lem_Basic_classes

/- 1. THE core probe (the sem:S2 shape): prio_pair has a MODEL Eq
   instance (first-field-only, default priority = 1000) AND the
   backend's auto Eq0 trio (structural, priority := 500). The model
   instance must win BY PRIORITY: first fields equal, second differ ->
   isEqual = true iff the model instance decided. Pre-B4 this held only
   by newest-declaration-first ORDER (both at 1000) — the accident this
   probe permanently pins away. -/
#guard Eq0.isEqual (Prio_pair 0 1) (Prio_pair 0 2) == true
#guard Eq0.isInequal (Prio_pair 0 1) (Prio_pair 0 2) == false
/- ... and the model instance still distinguishes first fields. -/
#guard Eq0.isEqual (Prio_pair 1 0) (Prio_pair 2 0) == false

/- 2. No-model-instance leg: prio_auto's Eq0 must resolve to the auto
   trio (structural, 500) — above the generic low defaults and the
   failwithI-bodied fallbacks (a fallback would PANIC here, failing the
   build loudly under the guard's evaluation). -/
#guard Eq0.isEqual (Prio_auto 0 1) (Prio_auto 0 2) == false
#guard Eq0.isEqual (Prio_auto 0 1) (Prio_auto 0 1) == true

/- 3. Auto-wins-where-no-model, ordered classes: prio_pair declares NO
   Ord0/SetType instance, so the auto trio's structural order decides
   (second field 1 < 2). -/
#guard Ord0.isLess (Prio_pair 0 1) (Prio_pair 0 2) == true
#guard (match SetType.setElemCompare (Prio_pair 0 1) (Prio_pair 0 2) with
        | LemOrdering.LT => true | _ => false) == true
