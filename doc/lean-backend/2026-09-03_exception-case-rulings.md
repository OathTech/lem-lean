# Exception-case rulings — X1 and X3/N4 (2026-09-03)

Resolves `2026-09-03_parity-fix-record.md` §4 ("EXCEPTION-CASE arguments
for the operator (not decided here)") for the two cases still open after
X2 and X4 were fixed as class-(c) generation-time refusals (the
`LemUnsupported.` marker hook, `3c88f0d`). Docs-only; no code changes.

## 1. The rule and the ruling

The standing rule [USER 2026-09-03]: "there should be ZERO discrepancies
between the ocaml reference and Lean in terms of behavior. All such
discrepancies are definitionally bugs (unless there is an extraordinarily
compelling case why this would not work - which should be made now, all
legacy permission revoked as of now)". Accepted exception classes: (a)
failure-path message text; (b) resource limits (Lean must not fail where
OCaml succeeds); (c) missing features refused at generation time.

The operator asked "for the lem-lean cases, are these bugs in
lem-upstream?" The orchestrator's [AGENT] answer, put to the operator
2026-09-03 (verbatim excerpts):

> Not bugs in the sense of "upstream got it wrong" — and the check
> reframes both in a way that fits your rule better than "exception"
> does.
>
> 63-bit `nat`/`int`: a documented design compromise in upstream lem,
> not a bug. […] lem's semantics — as realized by its HOL, Isabelle and
> Coq backends — is unbounded, and the OCaml backend is the deviant, by
> explicit upstream choice. The Lean target (`nat → Nat`) sits on the
> theorem-prover side. Under "follow the LEM semantics," this isn't an
> exception to the rule; it's the rule applied […] The raising
> conversions we fixed are consistent with what OCaml itself does at the
> boundary. Nothing to file; at most a one-line note in the eventual lem
> submission that the Lean backend follows the prover-side reading.
>
> Polymorphic compare on closure-carrying values: an OCaml-backend
> representation artifact, worth an upstream note. Lem's mathematical
> semantics defines set equality; the OCaml backend represents sets as
> records carrying a comparator closure, so OCaml's structural
> `=`/`compare` raises `Invalid_argument "compare: functional value"` on
> any value containing one. Lean compares structurally and succeeds —
> again matching the prover-side semantics. […] it belongs in the lem
> submission bundle as a known-limitation report with the reproducer,
> not as a lem-lean action.
>
> So for the census I'd record both not as "exceptions" but as
> "OCaml-backend deviations from lem's own semantics; the Lean target
> follows lem (prover-side); parity is not required in the OCaml→Lean
> direction here".

[USER 2026-09-03], verbatim: "Agree re lem." — the framing above is the
ruling.

## 2. Disposition

Both cases are classified as **OCaml-backend deviations from lem's own
semantics; the Lean target follows lem (prover-side); parity is not
required in the OCaml→Lean direction here.** They are NOT exception
classes (a)–(c) and do not widen them.

### X3 / N4 — `nat`/`int` are 63-bit machine integers on the OCaml target

- lem's normative statement, `library/num.lem:104-111`, verbatim:

  > "nat" is the old type "num". It represents natural numbers.
  > These numbers might be bounded, however no checks of the boundedness
  > are provided. The theorem prover backends map nat to unbounded size
  > natural numbers. However, OCaml uses the type "int", which is bounded.
  > Using "int" allows using many functions like "List.length" without
  > wrappers. This leeds to nice readable code, but a slightly fuzzy
  > concept what "nat" represents. If you want to use unbounded natural
  > numbers, use "natural" instead.

- Lean `nat → Nat`, `int → Int` (unbounded) is the prover-side reading;
  the silent wrap of `+`/`*`/`abs` above 2^62 on OCaml (parity record N4,
  measured: `maxint+1 -> -4611686018427387904`) is the OCaml backend's
  documented compromise and is NOT mirrored.
- The checked conversions landed at `3c88f0d` (`natFromNatural`,
  `natFromNumeral`, `intFromInteger`, `intFromNumeral` fail loudly
  outside [-2^62, 2^62-1], where `Nat_big_num.to_int` raises
  `Failure "int_of_big_int"`) STAY [AGENT]: at that exact boundary the
  OCaml reference fails, so both targets fail (the rule's direction is
  preserved); this is the one place where the Lean target sides with the
  OCaml boundary rather than the prover reading, recorded here as a
  deliberate, revisitable choice — no lem semantics assigns a value there
  for the OCaml target, and a value ≥ 2^62 is unreachable in cerberus's
  model (its C arithmetic lives in `integer` = Z).
- Upstream: nothing to file. The lem submission carries a one-line note
  that the Lean backend follows the prover-side reading of `nat`/`int`.
- Tests: the conversion checks are pinned by the parity runner
  (`f_int_of_big_num`, both-fail); the arithmetic wrap has no runner row
  by design (a runner row would pin a known non-parity), the measurement
  is quoted in the parity record's N4 row.

  **Addendum 2026-09-04 (fuel-parameter arc, commit on branch
  `arc/fuel-parameter`) — the "conversion checks STAY" sentence above is
  SUPERSEDED.** [USER 2026-09-03], verbatim: "ocaml limits that are
  hardcoded thanks to ocaml-level execution issues are also forbidden,
  the real thing is the logical semantics". The 63-bit checks in
  `lemNatFromNatural`/`lemIntFromInteger` (added at `3c88f0d`) were an
  OCaml-execution artifact, not lem's semantics: REMOVED; both
  conversions are the identity on Lean's unbounded `Nat`/`Int`, end to
  end (`natFromNumeral`/`intFromNumeral` were already literal
  pass-throughs). The parity row `f_int_of_big_num` is now a registered
  OCaml-target deviation in `tests/comprehensive/parity/expected_failures.txt`
  (entry class 2, citing this addendum): the runner requires it to fail
  parity (Lean succeeds where the OCaml reference raises) and reports it
  XFAIL. Other LemLib behaviours examined under the same principle
  (listed in `2026-09-04_fuel-parameter-record.md` §7): the `int32`/`int64`
  fixed-width WRAP is lem's declared semantics (stays); the loud failures
  that mirror OCaml *raises* (division by zero, `Z.sqrt` of a negative,
  `of_string` of an invalid literal, `Not_found`, `Invalid_argument
  "Array.sub"`) are failure-parity items under exception class (a), not
  limits (stay); the `Nat_big_num.to_int32/to_int64: Overflow` raise on
  `int32FromInteger`-style conversions is a candidate of the same kind as
  X3 (the prover-side reading is `word_of_int`, i.e. wrap) and is put to
  the operator in the record's decisions section, unchanged here.

### X1 — polymorphic compare on values containing a set or map

- OCaml `compare`/`=` on a `Pset`/`Pmap` value raises
  `Invalid_argument "compare: functional value"` (the record carries a
  comparator closure; `compare` on physically identical closures excepted);
  Lean's structural `BEq`/`Ord (Pset α)` instances compute. Lem's
  semantics defines set equality mathematically (`setEqual`, comparator-
  keyed on both targets); the raise is a representation artefact of the
  OCaml target.
- Code-side record: the in-code note at the instances,
  `lean-lib/LemLib.lean:741-748` (already in place; it states the OCaml
  behaviour and that lem's own set equality is the comparator-keyed
  `Pset.equal`). No change.
- Upstream: a known-limitation report with a reproducer goes into the lem
  submission bundle; whether upstream files it as a bug or documents it is
  theirs to decide. Not a lem-lean action.
- Tests: not probed (a probe needs a cerberus-shaped type carrying a set
  field and a structural `=` on it); the submission-bundle reproducer will
  be written when the bundle is assembled.

### X2 / X4 — closed before this ruling

Fixed at `3c88f0d` as class-(c) generation-time refusals (parity record
§3 rows X2, X4; `negative/neg_unsupported_*.lem`). The residual question
in X4 — whether `real`/`float64` should be SUPPORTED on Lean `Float`
instead of refused — was not put to the operator today and stays in
`TODO.md` as an open item.

## 3. Provenance

[USER 2026-09-03]: the rule (§1) and the ruling "Agree re lem." [AGENT]
(orchestrator): the framing quoted in §1, the disposition wording of §2,
the decision to keep the conversion checks, the upstream-note plan.
[AGENT] (parity-fix worker, `3c88f0d`): the measurements quoted from the
parity record. Nothing was merged or pushed in this slice.
