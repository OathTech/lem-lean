/- Hand-written pins for the supply-lifting feature (effect-retirement
   arc; see test_supply.lem / test_supply_multi.lem). A lifted def
   cannot be referenced from a .lem assert (the fail-closed net rejects
   supply constants outside threaded code at generation time), so the
   draw-sequence and signature pins live here.

   The `example ... := rfl` rows are KERNEL-checked draw-order pins:
   they are the charter-O1 evidence that the transform sequences draws
   in left-to-right depth-first (strict evaluation) order, with exact
   successor numbering — supplySplit s = (s, s+1), nothing skipped,
   nothing reordered. -/

import Test_supply
import Test_supply_multi

/- === signature pins: binder order is [readers] [supply] [args];
   result is the value×supply pair === -/
example : Nat → Unit → (Nat × Nat) × Nat := draw_two
example : Nat → Nat → Unit → Nat × Nat := both        -- reader THEN supply
example : Nat → Nat → Nat → Nat × Nat := seeded       -- supply then seed arg
example : Nat → Nat → List Nat × Nat := fuel_draws    -- wrapper: supply then arg
example : Nat → Nat → Unit → (Nat × Nat × Nat) × Nat × Nat := two_streams

/- === draw-sequence pins (kernel-checked, exact numbering) === -/
example : draw_two 100 () = ((100, 101), 102) := rfl
example : draw_list 5 () = ([5, 6], 7) := rfl
example : mk_wrap 3 () = (Wrap 3 4, 5) := rfl
example : mk_srec 7 () = ({ ra := 7, rb := 8 }, 9) := rfl
example : read_ra 7 () = (7, 9) := rfl
example : sum_two 10 () = (21, 12) := rfl

/- control forms: only the taken branch consumes -/
example : branchy 50 true = (50, 51) := rfl
example : branchy 50 false = (0, 50) := rfl
example : matchy 20 (some 5) = (25, 21) := rfl
example : matchy 20 none = (20, 21) := rfl

/- multi-clause source (pattern-compiled to one match) threads -/
example : clausy 20 (some 5) = (25, 21) := rfl
example : clausy 20 none = (20, 21) := rfl

/- threaded calls / transitive lifting -/
example : uses_draw_two 100 7 = (208, 102) := rfl

/- destructuring RHS evaluates once: pair_draw's two draws happen
   exactly once, then c draws the next id (a duplicated RHS would give
   c = 34, not 32) -/
example : pair_draw 30 () = ((30, 31), 32) := rfl
example : destructure_once 30 () = ((30, 31, 32), 33) := rfl

/- top-level multi-name destructuring (the L0 single-RHS emitter):
   each projection makes ONE threaded call of the shared RHS def —
   within a call the RHS draws exactly once (top_a's final supply
   is 502, two draws, not four) -/
example : top_a 500 = (500, 502) := rfl
example : top_b 500 = (501, 502) := rfl

/- reader × supply composition (reader injected, supply threaded) -/
example : both 9 40 () = (49, 41) := rfl
example : uses_both 9 40 3 = (52, 41) := rfl

/- reader_seed × supply: the seed argument (42) feeds the reader
   injections; the supply threads through the seed def's own binder -/
example : seeded 40 42 3 = (85, 41) := rfl
example : uses_seeded 40 3 = (85, 41) := rfl

/- fuel × supply: the worker threads the supply through the
   decremented self-call -/
example : fuel_draws 60 2 = ([60, 61], 62) := rfl
example : uses_fuel_draws 60 2 = ([60, 61, 62], 63) := rfl
/- fuel exhaustion returns the sentinel with the supply UNCONSUMED at
   the exhaustion point (one draw happened before fuel ran out) -/
example : fuel_draws_lemFuel 1 60 2 = ([60], 61) := rfl

/- === multi-supply ordering (test_supply_multi.lem): binders sorted
   by name (tick before tock); each draw advances only its own
   stream; result states in the same order === -/
example : two_streams 10 100 () = ((10, 100, 11), 12, 101) := rfl
example : uses_two_streams 10 100 () = ((11, 101, 12), 12, 101) := rfl
