# Fuel-parameter arc — lem half, record (2026-09-04)

Branch `arc/fuel-parameter` (lem-lean), base mainline `mdd/lean-backend`
@ `0890229` + the design note (`774569c`) + the operator's general form
(`0db35ec`). Charter: `2026-09-03_fuel-parameter-design.md` (§4 lists the
questions settled here; its R1 section carries the deltas from the
draft). Worker [AGENT] (lem-lean); rulings [USER 2026-09-03] quoted
verbatim; every quoted output is verbatim from this tree; tallies marked
"derived" are derived. Nothing merged, nothing pushed.

## 0. Commits

| Commit | Content |
|---|---|
| `d80505b` | Backend: fuel is the `[LemFuel]` instance (fuel lifting = the reader fixpoint with an instance-implicit binder); numeric budgets + `lemDefaultFuel` deleted; `fuel_consumer` declare; generated `f_lemFuel_zero` lemmas; fuel scope net; gate; tests; manual/DESIGN/README; design note R1 |
| `b18715f` | Zero lemma also for typed/parenthesised parameter patterns (cerberus: 67/67) |
| `16fe2ff` | LemLib: `Pset.join`/`Pmap.join` height-indexed structural (kernel-computable); `heightsOk`; `join_eq` theorems; closed-term `decide` tests |
| `22a2b17` | LemLib: `natFromNatural`/`intFromInteger` identity (63-bit OCaml checks removed); `f_int_of_big_num` a ruled OCaml-target deviation; X3 addendum |
| (this record's commit) | record, TODO rows 10–14 |

## 1. The rulings this slice implements

- [USER 2026-09-03] "fuel is an execution parameter that 'doesn't matter'
  — that is, any fuel value can be chosen [...] this and all other magic
  values are completely forbidden [...] fuel [is] a parameter which can be
  chosen as 10^8 or any other value when calling the interpreter"; "All
  similar such magic values should be removed and replaced by quantified
  parameters"; "the lemlib bounds are fine if they are passed as
  parameters to the semantics and can be chosen by a calling context.
  Otherwise they are forbidden magic values."
- General form [USER 2026-09-03]: "Generally, any instance of a value
  that can be quantified over by a context / theorem is fine. Defaults
  that are chosen eg. in test suites are fine. Any and all magic values
  that are hardcoded and can't be quantified over are definitionally bugs
  (unless they mirror lem or ISO-C design choices)".
- Third form [USER 2026-09-03]: "my aim here is to forbid values that
  limit the semantics or limit the ways the customer can reason about the
  semantics. It doesn't seem like this proposal does that?" — structural
  recursion on a DATA measure is admissible.
- [USER 2026-09-03] "ocaml limits that are hardcoded thanks to ocaml-level
  execution issues are also forbidden, the real thing is the logical
  semantics".

Every value touched below is classified against the general form: a
caller parameter (quantifiable), a test-suite choice (fine), a data
measure / termination proof (nothing chosen), lem's own semantics (not
magic), or an OCaml-execution limit (forbidden).

## 2. Design decisions (the design note's §4, plus what the build forced)

**§4.1 Mechanism — the ambient fuel is a LemLib class, taken as an
instance-implicit binder.** `class LemFuel where fuel : Nat`
(`lean-lib/LemLib.lean`). A fuel'd `f` emits the total worker
`f_lemFuel (lemFuel : Nat) …` (unchanged), the wrapper
`def f [LemFuel] : T := f_lemFuel LemFuel.fuel`, and the lemma
`theorem f_lemFuel_zero … : f_lemFuel 0 … = <sentinel> := rfl`. Every
definition that (transitively) reaches a fuel'd constant, a fuel-lifted
definition or a `{lean} fuel_consumer` takes `[LemFuel]`
(`lean_fuel_prepass`, `src/lean_backend.ml`: the reader-lifting fixpoint
at `Val_def` granularity, instances skipped, `reader_seed` defs INCLUDED,
target_rep'd defs excluded). Call sites are textually unchanged (instance
resolution passes the binder); bare/HOF references need no repair; the
entry point supplies `@f ⟨n⟩ …` or `letI : LemFuel := ⟨n⟩`; a theorem
quantifies `∀ [LemFuel]` or over `n` (`@f ⟨n⟩ = f_lemFuel n` by rfl).

Reasons, and the alternatives rejected: (a) an explicit `(_lemFuel : Nat)`
reader-style binder threaded at every call site — built first
(0db35ec-dirty, not committed): it changed the text of every call of a
fuel'd function, needed the partial-application repair for HOF uses, and
needed an injection rule for hand-written reps; the consumer's first
requirement ("a single parameter — module-level or a typeclass-style
instance argument — not per-signature threading") rules it out. (b)
folding fuel into the reader parameter list — couples fuel to
`reader_seed` (one seed argument cannot seed two ambients) and gives a
reader-only def a fuel binder. (c) a module-level `variable [LemFuel]` —
Lean includes section variables by header mention only; fragile and
per-file. (d) a global `opaque`/constant fuel — not quantifiable: the
defect itself. A hazard the class form has that (a) has not: a stray
global `instance : LemFuel` would silently give every fuel'd function a
default; the gate (§8.4) forbids one in LemLib and in generated code.

**A worker takes `[LemFuel]` only when it passes the ambient on.** The
block's bodies are scanned for fuel outside the block (`workers_need_fuel`,
all-or-none per `let rec … and` block, like the counter); a leaf worker's
only fuel is its counter, so its theorems carry no instance. Every fuel'd
callee starts from the FULL ambient, never from the caller's remaining
counter (the design note's §3 sentence; pinned by
`TestFuelParamCheck` (5): `@outer ⟨4⟩ 3 = 0`).

**§4.2 Hand-written reps that call `_lemFuel` workers: `declare {lean}
fuel_consumer val f`.** The rep's implementation takes `[LemFuel]` and
reads `LemFuel.fuel`; the declare makes its callers fuel-lifted; call
sites are unchanged (guards FC-rep: must carry a Lean target_rep;
FC-inert: a fuel SENTINEL on a rep'd val is refused). For cerberus: each
`mem.lem` consumer whose `CerbMem` implementation reaches a `_lemFuel`
worker gets `declare {lean} fuel_consumer` beside its `reader_consumer`,
and the implementation replaces `lemDefaultFuel` by `LemFuel.fuel` (§6).
The draft's "the memory model's ambient record carries it" was rejected:
it makes two fuels (the record's and the generated code's).

**§4.3 A fuel'd function referenced with no ambient fuel in scope** —
a lem `assert`, an indreln rule, an instance method — is a generation-
time error naming the site (`fuel_scope_check` at the three reference
sites; the instance guard mirrors the reader lifting's). There is no
default to inject, by design. A LIBRARY assert renders as a
removed-comment instead (the library's `_auxiliary.lean` files are
deleted by `make lean-libs`; measured on relation.lem's
`withoutTransitiveEdges` rows while the caller-fuelled `tc` variant was
built). Consequence measured on cerberus: three `Eq` instances and one
indreln rule hit the guard (§6) — an OPERATOR/consumer decision (§9).

**§4.4 Perf** — §7.

**§4.5 LemLib** — §4 (table).

**Deleted** (the defect itself): the numeric form `declare {lean} fuel
val f = N` — the parser production is kept only to refuse it with its
reason (`Parse_error_locn`, negative `neg_fuel_numeric_budget`; a bare
syntax error would not say why); `const_descr.fuel_budget` (replaced by
`fuel_consumer : Targetset.t` — one field out, one in), `Decl_fuel_budget`
/ `Decl_fuel_budget_decl` (→ `Decl_fuel_consumer`), the human-target echo
of the budget, `lean_fuel_budget_check`, `lean_fuel_budget_completeness_check`,
`fuel_budget_for`, the `lemDefaultFuel` reserved-def-name guard (the name
has no meaning to the backend any more; `LemFuel` joins
`library/lean_constants` so a user type/def of that name is renamed);
`def lemDefaultFuel : Nat := 1000000` (LemLib HISTORY note remains);
`test_fuel_budget.lem`, `TestFuelBudgetExec.lean`, phase
`lean-fuel-budget`, `neg_fuel_budget_{nosentinel,rep,speconly,zero}.lem`,
`neg_default_fuel_name.lem`, `inv_fuel_budget.lem` (→ `inv_fuel.lem`);
the `fuel_draws_b` budget rows of `test_supply.lem`, `p_supply_shapes`
(pin edited: the OCaml reference row removed, runner confirms the pin
matches), `TestSupplyCheck/Draws`. Grammar: `language/lem.ott` row
`fuel_budget_decl` → `fuel_consumer_decl`. ocamlyacc at the final
grammar, verbatim: `5 rules never reduced` / `2 shift/reduce conflicts,
2 reduce/reduce conflicts.` — unchanged from the baseline.

## 3. Before / after — one fuel'd function, verbatim

`tests/comprehensive/test_target_reps.lem`, ``declare {lean} fuel val
fuel_countdown = `999` `` and its caller. BEFORE (lem `0db35ec`,
`Test_target_reps.lean:459-468`):

```lean
 def  fuel_countdown_lemFuel (lemFuel : Nat)  (n : Nat)  : Nat := match lemFuel with
  | 0 => (999)
  | Nat.succ lemFuel => (
  if  n  ==   0 then   0  else (fuel_countdown_lemFuel lemFuel)  (n  -   1))

def fuel_countdown : Nat → Nat := fuel_countdown_lemFuel lemDefaultFuel

def  uses_countdown   (k  : Nat)   :  Nat :=  fuel_countdown  k  +   1
```

AFTER (this lem, `Test_target_reps.lean:459-470`):

```lean
 def  fuel_countdown_lemFuel (lemFuel : Nat)  (n : Nat)  : Nat := match lemFuel with
  | 0 => (999)
  | Nat.succ lemFuel => (
  if  n  ==   0 then   0  else (fuel_countdown_lemFuel lemFuel)  (n  -   1))

def fuel_countdown [LemFuel] : Nat → Nat := fuel_countdown_lemFuel LemFuel.fuel
theorem fuel_countdown_lemFuel_zero ( n : Nat) :
    fuel_countdown_lemFuel 0  n = (999) := rfl

def  uses_countdown [LemFuel]   (k  : Nat)   :  Nat :=  fuel_countdown  k  +   1
```

The worker is byte-identical; the wrapper's numeral became the ambient;
the caller gained the binder and nothing else. A worker that passes the
ambient on (cerberus `driver2_lemFuel`, `outer_lemFuel` in
`test_fuel_param.lem`) reads `def driver2_lemFuel [LemFuel] (lemFuel : Nat) …`.

## 4. LemLib — every bounded recursion, classified (the operator's aim as the test)

Test: "forbid values that limit the semantics or limit the ways the
customer can reason about the semantics". Forms: (a) caller parameter,
(b) termination proof (well-founded), (c) data-measure structural
recursion.

| Function (`lean-lib/LemLib.lean`) | Before | Now | Form | Theorem |
|---|---|---|---|---|
| `lemDefaultFuel` | `1000000` | DELETED | — (was magic) | — |
| `Pset.join`, `Pmap.join` | WF on `sizeOf l + sizeOf r` | `joinGo` indexed by `height l + height r + 1` | (b) → (c): kernel-computable | `LemLibTheorems.PsetJoin.join_eq`, `PmapJoin.join_eq` (under `heightsOk`; axioms `[propext, Classical.choice, Quot.sound]`) |
| `Pset.unionGo/interGo/diffGo/subsetGo`, `Pmap.mergeGo` | index `height s1 + height s2 + 1` | unchanged, reclassified | (c) | none needed (no rewrite) |
| `Pset.compareAux`, `Pmap.equalAux`, `Pmap.compareAux` | index `cardinal s1 + cardinal s2 + 1` | unchanged, reclassified | (c) | none needed |
| `Pset.tc` | `lfpGo … ((2n)(2n) + 1)` | unchanged, reclassified; a caller-fuelled variant via `fuel_consumer` on `Relation.transitiveClosureByCmp` was BUILT and WITHDRAWN (§9 D1) | (c) — flagged | — |
| `Pset.lfpGo` | fuel-taking primitive | unchanged; documented as the caller-fuelled primitive whose one caller (`tc`) supplies a data measure | (a) | — |
| `lemLeastFixedPoint` | `bound` from lem, `\| 0 => x` silent | unchanged | lem's own `Set.leastFixedPoint` (set.lem:709 `\| 0 -> x`) — not magic, not ours to change alone (§9 D3) | — |
| `gen_pow_aux`, `listSet`, `boolListFromNatural`, `bitSeqBinopAux`, `lemStringFromNatHelper`, `lemStringFromNaturalHelper` | WF (`exp`, `remainder`, list lengths, `n`) | unchanged | (b) — admissible; blocks kernel computation like `join` did | TODO row 12 |
| `natFromNatural` / `intFromInteger` | fail outside ±2^62 (OCaml limit) | identity | OCaml-execution limit REMOVED | — |

`Pset.heightsOk`/`Pmap.heightsOk` (Bool) are new: the invariant the
height index relies on, and the predicate the consumer's Pmap-laws slice
builds on. Zero-axiom census: `grep -rn "^axiom " lean-lib/ --include="*.lean"`
→ no hits (exit 1). Kernel-only methods throughout (`rfl`, `decide`,
`omega`, `simp`); no `native_decide`, no heartbeat/maxRecDepth option
anywhere. Kernel-computability evidence (scratch, verbatim):
`Pset.elements (Pset.join cNat (Pset.fromList cNat [1, 2]) 3 (Pset.fromList cNat [4, 5, 6, 7])) = [1, 2, 3, 4, 5, 6, 7] := by decide`
succeeds; the same over `PsetJoin.joinSpec` (the WF form): "Tactic
`decide` failed for proposition … did not reduce to `isTrue` or
`isFalse`". `LemLibTest.lean` decides closed terms through
`Pset.union/inter/diff/remove`, `Pmap.union/remove`, `fmapUnionBy`,
`fmapDeleteBy`.

## 5. Exhaustion and monotonicity (consumer requirements 2–3)

Generated: `f_lemFuel_zero` for every fuel'd function whose parameters
are variables, `(x : t)` annotations, parenthesised variables or
wildcards — lem's pattern compiler makes them so (a source `let rec f
(a, b) = …` arrives as `f p = match p with …`); the "not generated"
comment path is a backstop no lem source reached (cerberus: 67/67, §6).
The statement mirrors the worker's `| 0 =>` arm through one shared
renderer (`fuel_sentinel_output`), supply pairing included, so the two
agree by construction.

NOT generated — monotonicity ("completes at fuel f ⇒ identical at every
f' ≥ f"). What is true today: the unfolding equations `f_lemFuel.eq_1/2`
exist for every worker, and above the depth a program needs the value
is fuel-independent — a per-function, per-argument fact
(`TestFuelParamCheck.spin_sufficient`/`spin_fuel_irrelevant` show the
shape). What blocks a generic or generated theorem: (i) with the
convention's payload `fuelExhausted x` the sentinel is an OPAQUE value,
so "`f_lemFuel n x ≠ payload`" is not statable, let alone provable; (ii)
even with a distinguished value payload (`999`, cerberus's
`NDkilled fuelExhaustedKill`), "result ≠ payload at n ⇒ same result at
n+1" is FALSE in general — a body may absorb a sub-call's sentinel
(`if f (n-1) = 999 then 0 else …`) and change value once the sub-call
completes. Monotonicity is a property of how the body CONSUMES
exhaustion, not of the scheme. What it requires: an exhaustion outcome
that the return type distinguishes AND that every consumer of a recursive
result propagates (an absorbing element of the monad — cerberus's
`NDkilled` through `nd_bind` is exactly that); then the per-function
lemma follows by induction on the counter, and the backend could
generate it for functions whose payload is a DECLARED absorbing outcome
of a DECLARED monad — new vocabulary, an operator decision (TODO row 13).

## 6. Cerberus dry run (read-only; scratch copy of `frontend/**/*.lem` at cerberus-lean `HEAD`)

Method: `.tmp/cerb/run.sh` — the cerberus Makefile's exact flags
(`-wl ign -wl_rename warn -wl_pat_red err -wl_pat_exh warn -cerberus_pp`)
and its expanded `LEM_SRC` (87 files) / `LEM_SRC_LEAN` (86), obtained
with `make --eval` (read-only); OCaml with the baseline lem (`0db35ec`,
saved binary) and with this lem; Lean with this lem.

1. **The five numeric declares are refused on every target**
   (`driver.lem:1915-1918` `print_eval_conv_aux`,
   `drive_nonmemory_steps_aux2`, `driver2`, `hack` = 100000000;
   `nondeterminism.lem:574` `nd_bind` = 100000000), verbatim: `Syntax
   error: the numeric fuel-budget form 'declare {lean} fuel val f = N'
   was removed (fuel-parameter arc, 2026-09-04) …`. The cerberus half
   DELETES those five lines (fail-closed: `lem` refuses the sources until
   it does; the sentinel declares on the same five vals stay).
2. **OCaml byte-identity.** Same sources (the scratch copy with the five
   lines deleted), baseline lem vs this lem: `files: base=86 new=86` /
   `OCAML DIFF exit 0 lines 0` (`diff -r`, verbatim). Baseline lem on the
   ORIGINAL sources vs this lem on the edited sources: one hunk,
   `driver.ml:2308a2309,2313`, a 5-line source comment (`(* FUEL arc budget
   commit … *)`) that the original's `declare` line SWALLOWED — non-human
   targets emit `emp` for a `{lean}` declare, leading skips included — and
   that now attaches to the next definition. Not a backend change; a
   pre-existing quirk of every `{lean}` declare, noted.
3. **Lean generation** succeeds (`new-lean exit 0`, 170 files) once four
   more source sites are addressed — measured by patching the SCRATCH
   copy only, each recorded:
   - `ctype.lem:183` `instance (Eq ctype) let (=) = ctypeEqual` — fuel'd
     equality as an instance method (error: "fuel'd (or fuel-lifted) call
     inside an instance method");
   - `core.lem:91-92` `instance (Eq core_base_type)` via `eq_core_base_type`;
   - `defacto_memory_aux.lem:38-39` `instance (Eq mem_value)` via
     `fake_mem_value_eq`;
   - `cmm_op.lem:580` indreln rule `monStep`: premise
     `Nondeterminism.mem ((a: action), z) (monStep pre y)` references the
     fuel-lifted `monStep` (error: "referenced outside a fuel scope").
   These are the §9 D2 decision (instance-level `[LemFuel]` in the
   backend vs restructuring in the model).
4. **Counts on the complete tree (derived, `grep`):** fuel-declared vals
   64 (69 declares minus the 5 numeric); wrappers at the ambient
   `:= f_lemFuel LemFuel.fuel` **67 in 15 files** (the design note's
   "77 sites in 16 files" was a grep for `lemDefaultFuel` over cerberus's
   `lean_frontend/generated/`, which also holds the hand-written copies —
   `CerbMem.lean` alone has 12 such sites; measured today on that tree:
   73 `_lemFuel lemDefaultFuel` occurrences in 15 files); `f_lemFuel_zero`
   lemmas **67**, "not generated"
   0; definitions taking `[LemFuel]` **370**; workers passing the ambient
   26, leaf workers 41; literal fuels after `_lemFuel` **0**;
   `lemDefaultFuel` **0**.
5. **The six sealed recursions the consumer named**, each now
   fuel-parametric (verbatim heads from the generated tree):
   `def driver2 [LemFuel] : … := driver2_lemFuel LemFuel.fuel` (the
   scheduler loop; `theorem driver2_lemFuel_zero [LemFuel] …`);
   `def drive_nonmemory_steps_aux2 [LemFuel] …` (the single-thread loop;
   its `_zero` lemma states the kill: `… = (fun _ => ND (fun st =>
   (NDkilled (Error0 CerbFuel.fuelExhaustedLoc CerbFuel.fuelExhaustedMsg),
   st))) := rfl`); `def hack [LemFuel] …` (the exit routine);
   `def print_eval_conv_aux [LemFuel] …` (the printing helper);
   `def nd_bind {a b c d e f : Type} [LemFuel] : ndM f b d a c → …`
   (the monad's bind; leaf worker, so `nd_bind_lemFuel_zero` has no
   instance); the expression-step recursions `step_eval_pexpr`,
   `eval_pexpr_aux2`, `full_eval_pexpr` (formerly at `lemDefaultFuel`):
   all `[LemFuel]` with `_zero` lemmas. `drive` is hand-written
   (`CerbND.lean:450`) and follows in the seam edit.
6. **Hand-written seams to change (the cerberus half's brief), file:line
   at cerberus-lean `HEAD`:**
   - `lean_frontend/CerbMem.lean` `lemDefaultFuel` call sites: `:483`
     (`memberAlign`), `:489` (`offsetsofMembers`), `:494` (`offsetsof`),
     `:498` (`sizeofCtype`), `:502` (`alignofCtype`), `:691`
     (`memValueToBytes`), `:849-850` (`memValueToBytes_eq_append` corollary),
     `:1016` (`reconstructValue`), `:1155-1156` (corollary), `:1183`
     (`typeofMval`), `:1215` (`unqualifyAndUnatomic`): each entry takes
     `[LemFuel]` and passes `LemFuel.fuel` to its `_lemFuel` worker; the
     `mem.lem` consumers whose implementations reach them
     (`sizeof_ival`/`alignof_ival`/`offsetof_ival` `:282-288`,
     `allocate_object`/`load`/`store` `:89-91`, and the pointer/memcpy
     family `:150-225` as their implementations require) add
     `declare {lean} fuel_consumer val …` beside `reader_consumer`.
   - `lean_frontend/CerbFuel.lean:71` `driverFuel : Nat := 100000000` and
     its doc `:53-61`: DELETE; the CLI keeps the only permitted numeral
     (`--fuel N`, default a harness choice) and builds `letI : LemFuel := ⟨n⟩`.
   - `lean_frontend/CerbND.lean`: `:85` `ndDefaultFuel := CerbFuel.driverFuel`
     DELETE; `:150`, `:227`, `:280` (`runND`, `runND1`, `runND1Trace` at
     `ndDefaultFuel`) become `[LemFuel]` entries; `:298-351` hand-written
     `_zero` theorems now DUPLICATE the generated ones (same names,
     `nd_bind_lemFuel_zero`, `liftND_lemFuel_zero`, … `memcmp_load_aux_lemFuel_zero`)
     — delete; `:389-413` `driverFuel_eq`, `*_wrapper_defeq`, `runND_eq`,
     `runND1_eq`: restate as `@f ⟨n⟩ = f_lemFuel n` or delete; `:450`
     hand-written `drive_lemFuel` copy gains `[LemFuel]` (calls
     `driver2_lemFuel fuel …`); `:467` `drive_wrapper_defeq` restated.
   - `lean_frontend/test/Unit/TotalityProofTest.lean:36-87` (52 `rfl`s
     "wrapper = worker at lemDefaultFuel"): restate as
     `∀ n, @f ⟨n⟩ = f_lemFuel n := fun _ => rfl` ("every fuel'd entry is
     fuel-parametric"). `EffectsProofTest.lean:55` (`zeros_aux` at
     `lemDefaultFuel`): same. `FuelExemplar.lean:204-205`
     (`budget_succ`, `lemDefaultFuel_succ`), `:222`, `:238-239`, `:253`,
     `:272`, `:317`: the exemplar becomes the ∀-fuel pattern.
   - `mem.lem` / `ctype.lem:183` / `core.lem:91-92` /
     `defacto_memory_aux.lem:38-39` / `cmm_op.lem:580`: the §9 D2 items.
7. **Restating a consumer hypothesis** (for the cerberus change
   manifest; refined-cerberus carries ~60 sites of the shape
   `potential e ≤ lemDefaultFuel`). Once the fuel is the caller's, the
   hypothesis is against the quantified fuel, not a constant: a statement
   `H e → step_eval_pexpr … e = r` that was proved under
   `potential e ≤ lemDefaultFuel` becomes
   `∀ [LemFuel], potential e ≤ LemFuel.fuel → step_eval_pexpr … e = r`
   (equivalently `∀ n, potential e ≤ n → @step_eval_pexpr ⟨n⟩ … e = r`,
   and for a closed executable `letI : LemFuel := ⟨n⟩`); the shipped-
   constant version is the corollary at `⟨100000000⟩`. The worker-level
   form the exemplar already uses (`f_lemFuel n …` with `n` explicit) is
   unchanged. The two constants (10^8 driver family, 10^6 the rest)
   collapse to ONE hypothesis variable.

## 7. Perf (design note §4.4; report, don't optimize)

Measured, not optimized. Two shapes:

1. **Clean Lean build of the comprehensive corpus** (LemLib + the
   `lean-test` package, `lake build` through `scripts/capped`, 32 cores):
   the BASELINE tree (`git archive 0db35ec`, generated by the baseline
   lem) vs the FINAL tree (`git archive HEAD`, this lem), `.lake` removed,
   sequential, two passes — verbatim:

   ```
   == base (47 sources generated by Lem 0db35ec): clean lake build, LemLib + test package
      exit 0, 8 s wall; Build completed successfully (134 jobs).
   == after (47 sources generated by Lem d80505b-dirty): clean lake build, LemLib + test package
      exit 0, 8 s wall; Build completed successfully (136 jobs).
   --- second pass (repeatability):
   == base (47 sources generated by Lem 0db35ec): clean lake build, LemLib + test package
      exit 0, 8 s wall; Build completed successfully (134 jobs).
   == after (47 sources generated by Lem d80505b-dirty): clean lake build, LemLib + test package
      exit 0, 7 s wall; Build completed successfully (136 jobs).
   ```

   The instance-implicit binder adds no measurable elaboration cost at
   this scale (+2 jobs are the new test modules). At run time the
   instance is one `Nat` argument (a single-field structure is represented
   as its field), the same shape the reader lifting already pays.
2. **The whole suite** (`make lean`, all phases incl. the two-target
   parity runner's 22 probe builds): baseline 3:16 wall (that run stopped
   at the parity phase — the fresh worktree had no `ocaml-lib/_build_zarith`,
   so parity contributed ~0 s); final 6:29.70 wall with the full parity
   leg (`make lean  389.71s user 42.89s system 111% cpu 6:29.70 total`);
   an intermediate incremental run (compile phase only re-touched) was
   1:14. Not comparable phase-for-phase; shape 1 is the controlled
   number. The cerberus-scale measurement (an extra instance argument on
   every fuel'd call in the differential lanes) belongs to the cerberus
   half, on its lanes' wall-clock, as the design note §4.4 says.

## 8. Gates — verbatim

### 8.1 tests/comprehensive `make lean` (final tree, `.tmp/final-comprehensive.log`)

```
=== Generation: 47 passed, 0 failed, 0 skipped ===
Build completed successfully (136 jobs).
=== Panic-path pin (failwithI raise at the L_undefined arm) ===
  OK (leg 1): panic prints the Incomplete Pattern message, then continues with default
  OK (leg 2): fail-stops (exit 134) under LEAN_ABORT_ON_PANIC=1
=== m7 single-evaluation pin (tuple-let RHS runs once) ===
  OK: draws: first=1 second=2
single-evaluation: OK
=== Supply draw-sequence pin (compiled) ===
  OK: compiled draw sequences hold
=== reader_consumer injection pin (compiled) ===
  OK: compiled consumer injection holds
=== Fuel as a quantified parameter (compiled): sufficient fuels agree; exhaustion is loud ===
  OK (leg 1): two sufficient fuels agree; insufficient gives the declared sentinel; callee starts from the full ambient
  OK (leg 2): loud exhaustion at an insufficient runtime fuel fail-stops (exit 134)
=== No fuel numerals in LemLib or generated code (gate) ===
  OK: 219 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F4)
=== Negative probes (must be rejected with the declared error) ===
  [45 × "OK (rejected as declared)" — derived count]
=== Non-Lean invariance ({lean} declares are no-ops for ocaml/hol/isa/coq) ===
  OK: inv_fuel.lem (7 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_reader_consumer.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
  OK: inv_supply.lem (5 artifacts byte-identical across ocaml/hol/isa/coq)
=== Two-target parity (OCaml reference vs Lean, compiled) ===
  [7 × "OK: both fail (…); stdout prefix identical", f_int_of_big_num
   "FAIL: failure probe, but the Lean binary SUCCEEDED (exit 0) where the
   OCaml reference fails" + "XFAIL (expected, registered): RULED
   OCaml-target deviation …", 21 × "OK: parity (N lines byte-identical to
   the OCaml reference; pin matches)" incl. p_fuel "(16 lines …)" and
   p_supply_shapes "(34 lines …)", p_str_bytes/p_str_escapes XFAIL (F2,
   pre-existing) — derived counts]
make lean  389.71s user 42.89s system 111% cpu 6:29.70 total
EXIT 0
```

The `p_fuel` leg, from the pin-recording run: `REBASELINED pin …/expected/p_fuel.out`
/ `OK: parity (16 lines byte-identical to the OCaml reference; pin
matches)` — the Lean driver printed `results` at fuels 200 and 100000,
the OCaml driver printed its fuel-free block twice.

### 8.2 lean-lib

`lake build` (capped): `Build completed successfully (37 jobs).`
`#print axioms`: `'LemLibTheorems.PsetJoin.join_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]`, same for `PmapJoin.join_eq`;
the twelve F7 theorems unchanged. `grep -rn "^axiom " lean-lib/
--include="*.lean"`: no hits.

### 8.3 tests/nonlean-regress (final tree)

```
nonlean-regress: OK (893 artifact rows, 216 exit rows, 9 emitters, byte-identical to golden)
```

(One intermediate variant — `fuel_consumer` declared on
`library/relation.lem` — made 37 `lib/tex`, 33 `lib/tex_all`, 1 `lib/lem`,
1 `lib/html`, 1 `lib/ident` rows drift, because the human/echo targets
re-render library source; that variant was withdrawn, §9 D1. No golden
was rebaselined in this arc.)

### 8.4 The gate, plant-tested (`tests/comprehensive/check_no_fuel_numerals.sh`)

Comments are stripped before matching (a HISTORY note may name the
deleted constant; a code token may not). Plants, verbatim:

```
PLANT 1 (F3: a generated worker applied to a literal fuel):
  FAIL (F3): fuel numeral shape found:
…/tests/comprehensive/Test_fuel_param.lean:132: def plant : Nat := spin_lemFuel 5 3
exit=1
PLANT 2 (F2+F4: a global instance in LemLib):
  FAIL (F2): fuel numeral shape found:
…/lean-lib/LemLib.lean:1793: instance : LemFuel := ⟨1000000⟩
  FAIL (F4): fuel numeral shape found:
…/lean-lib/LemLib.lean:1793: instance : LemFuel := ⟨1000000⟩
exit=1
PLANT 3 (F1: a code reference to the deleted default):
  FAIL (F1): fuel numeral shape found:
…/lean-lib/LemLib.lean:1793: def plant2 : Nat := lemDefaultFuel
exit=1
REVERTED:
  OK: 173 files scanned; no lemDefaultFuel, no LemFuel instance, no literal fuel (F1-F4)
exit=0
```

(173 files at plant time, before the parity `P_*.lean` modules existed
in the tree; 219 in the final run.) Excluded by design: test harnesses
and pins (`LemLibTest.lean`, hand-written `lean-test/Test*.lean`, parity
`Run_*`/`*.main.lean`) — a test suite may choose its fuel.

### 8.5 OCaml byte-identity of the comprehensive corpus

Baseline lem (`0db35ec`) vs this lem, `-ocaml` over every `test_*.lem`,
parity probe and invariance source (`LEMLIB` = this tree's library):
`ml files: base=102 new=103`; `diff -r` of the `.ml` trees:
`Only in .tmp/new-ocaml: inv_fuel.ml` (exit 1 for that one line: the
baseline lem cannot parse the new `fuel_consumer` declare — `inv_fuel.lem
1` vs `0` in the exit lists); every one of the 102 pre-existing `.ml`
files is byte-identical. The cerberus tree: §6.2.

## 9. Decisions for the operator (STOP-and-record items; nothing here was decided by me)

- **D1 — `Pset.tc`: data measure (as landed) or caller-fuelled?** The
  coordinator's brief said "lfp MUST be (a)". `lfpGo` (the primitive) IS
  caller-fuelled; its one caller `tc` passes `(2|r|)^2 + 1`, which I
  classified a data measure (the closure lives in the finite square of
  r's endpoints, so convergence within that many steps is a theorem for
  any total-preorder comparator) — the same form the operator ruled
  admissible for the height indices. The caller-fuelled alternative was
  BUILT: `declare {lean} fuel_consumer val transitiveClosureByCmp` in
  `library/relation.lem`, `set_tcByCmp [LemFuel]`, `tc [LemFuel]`;
  measured consequences: `Lem_Relation.reflexiveTransitiveClosureOn`,
  `withoutTransitiveEdges`, `Lem_Show_extra.stringFromRelation` gained
  `[LemFuel]`; the library assert `withoutTransitiveEdges_3` needed the
  library-assert exemption; 73 human/echo rows of the nonlean-regress
  golden drifted (a library source edit); `p_set_ops` needed a fuel. It
  was withdrawn [AGENT]. If the operator wants (a) for `tc` regardless,
  the withdrawn variant is a 4-line change plus the golden rebaseline.
- **D2 — fuel'd functions as instance methods / in indreln rules**
  (cerberus `Eq ctype`, `Eq core_base_type`, `Eq mem_value`; `monStep`
  rule). Options: (i) cerberus makes those equalities structurally
  recursive (`termination_argument`) — cleanest if Lean's structural
  checker accepts the nested-list recursion; (ii) backend: an instance
  whose methods reach fuel takes `[LemFuel]` (`instance [LemFuel] : Eq0
  ctype`) — mechanically small, but keeping the fail-closed property
  needs type-directed detection of class-method uses at fuel-lifted
  instances (the fixpoint sees `isEqual`, not the instance) — M; (iii)
  hand-written `instance [LemFuel]` via `skip_instances`, same gap. The
  indreln rule cannot take a binder at all: the concurrency model's
  problem to restate. Until decided the backend refuses fail-closed.
- **D3 — `lemLeastFixedPoint`'s silent `| 0 => x`** (the reasoning-
  artifact audit's remark). It is lem's own `Set.leastFixedPoint`
  (set.lem:709-715: `| 0 -> x`); the OCaml target computes exactly that.
  Making the Lean arm loud alone would be a Lean-vs-OCaml discrepancy
  (Lean fails where the reference succeeds) — the conflict between the
  audit's request and the zero-discrepancy rule is raised here, not
  resolved; a loud arm is an upstream (lem library) question. Other
  `| 0 =>` arms: every LemLib bounded recursion's is the loud
  `fuelExhaustedWith`; the backend's emitted `| 0 => <sentinel>` is the
  model author's payload — cerberus uses loud/typed payloads at 63 of 64
  declares and one silent VALUE payload
  (`defacto_memory_aux.lem:469` `simplify_integer_value_base` =
  ``Sum.inr ival_``, "returns its input unsimplified", its own comment
  says), noted for the cerberus half.
- **D4 — `int32FromInteger`-family Overflow raise** (X3 addendum): same
  shape as the removed 63-bit checks, but for lem's fixed-width types;
  wrap (prover-side `word_of_int`) or raise (zarith) — ruling needed;
  parity rows `f_int32_overflow`/`p_int_wrap` would move (TODO row 11).
- **D5 — the cerberus half's D2 choice shapes the pin bump**: with (i),
  no backend change; with (ii), one more lem slice before the bump.

## 10. Not done, and why

- Fuel monotonicity is not generated (§5: requires an absorbing typed
  outcome; TODO row 13).
- The remaining WF recursions of LemLib (§4 last row) are left as
  termination-proof form (admissible); converting them is TODO row 12.
- The Ott grammar file carries the new row; derived artifacts not
  regenerated (TODO row 5, pre-existing).
- `.tmp/` (baseline binary, scratch trees, logs) is ephemeral and
  deleted at slice end; everything load-bearing is quoted above.
