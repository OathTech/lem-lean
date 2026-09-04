LEM = ../../lem
LEMLIB = ../../library
LEMFLAGS = -wl ign -i $(LEMLIB)/pervasives.lem
# Every lake invocation runs through the cgroup cap (parity-fix audit
# response, 2026-09-03: "never run a Lean build uncapped"); the same
# variables the parity runner honours. Fail-noisy if the cap is absent.
CAPPED ?= /home/dev/projects/cerberus-lean-proj/cerberus-lean/scripts/capped
export CERB_MEM_MAX ?= 16G
LAKE = $(CAPPED) lake

TESTS = $(sort $(wildcard test_*.lem))

.PHONY: all lean lean-generate lean-compile lean-negative lean-panic lean-parity lean-fuel-param lean-no-fuel-numerals check-capped clean

check-capped:
	@test -x "$(CAPPED)" || { echo "FAIL: capped Lean runner '$(CAPPED)' not found or not executable (set CAPPED=...)"; exit 1; }

all: lean

# === Lean Backend ===

lean: lean-generate lean-compile lean-panic lean-tuple-once lean-supply-draws lean-reader-consumer lean-fuel-param lean-negative lean-invariance lean-parity lean-no-fuel-numerals

# Two-target parity (parity-fix slice 2026-09-03; [USER] ruling: the OCaml
# target is the reference semantics of a lem program, the Lean target
# must compute the same thing, zero discrepancies). parity/run.sh builds
# an OCaml binary AND a Lean binary from each parity/probes/*.lem, runs
# both, diffs stdout byte-for-byte, and checks the OCaml output against
# its committed pin (parity/expected/). Failure probes (f_*) must fail on
# both targets. Needs the opam switch in PATH (scripts/ce) — the OCaml
# leg is what makes this a parity test rather than a self-consistency
# check (the retired M2 scaffold compared hand-measured values).
lean-parity:
	@echo "=== Two-target parity (OCaml reference vs Lean, compiled) ==="
	@./parity/run.sh

# Fuel as a quantified parameter (fuel-parameter arc, 2026-09-04;
# [USER 2026-09-03] "fuel is an execution parameter that 'doesn't
# matter'"): compiled witnesses that two different sufficient fuels give
# identical results, that an insufficient fuel gives exactly the declared
# sentinel, that a fuel'd callee starts from the FULL ambient, that a
# fuel_consumer reads the same ambient, and (leg 2, under
# LEAN_ABORT_ON_PANIC=1) that a loud sentinel at an insufficient RUNTIME
# fuel fail-stops the process at the program point.
lean-fuel-param:
	@echo "=== Fuel as a quantified parameter (compiled): sufficient fuels agree; exhaustion is loud ==="
	@cd lean-test && $(LAKE) build test-fuel-param > /dev/null
	@out=$$(cd lean-test && ./.lake/build/bin/test-fuel-param 2>&1); st=$$?; \
	if [ $$st -ne 0 ]; then \
		echo "  FAIL (leg 1, exit $$st):"; echo "$$out"; exit 1; \
	elif ! echo "$$out" | grep -q "fuel param: OK"; then \
		echo "  FAIL (leg 1): no OK line"; echo "$$out"; exit 1; \
	else \
		echo "  OK (leg 1): two sufficient fuels agree; insufficient gives the declared sentinel; callee starts from the full ambient"; \
	fi
	@out=$$(cd lean-test && LEAN_ABORT_ON_PANIC=1 ./.lake/build/bin/test-fuel-param --exhaust 2>&1); st=$$?; \
	if [ $$st -eq 0 ]; then \
		echo "  FAIL (leg 2): exited 0 under LEAN_ABORT_ON_PANIC=1 (exhaustion did not fail-stop)"; \
		echo "$$out"; exit 1; \
	elif echo "$$out" | grep -q "survived:"; then \
		echo "  FAIL (leg 2): execution continued past the exhaustion under LEAN_ABORT_ON_PANIC=1"; \
		echo "$$out"; exit 1; \
	elif ! echo "$$out" | grep -q "fuel exhausted"; then \
		echo "  FAIL (leg 2): fail-stopped without the fuel-exhausted message"; \
		echo "$$out"; exit 1; \
	else \
		echo "  OK (leg 2): loud exhaustion at an insufficient runtime fuel fail-stops (exit $$st)"; \
	fi

# No fuel numeral anywhere it could be magic (fuel-parameter arc gate;
# plant-tested, see check_no_fuel_numerals.sh): LemLib, the generated
# library, every generated test module — no `lemDefaultFuel`, no
# `instance … : LemFuel`, no worker applied to a positive numeral, no
# `LemFuel := ⟨N⟩`. The only permitted shape of a fuel is a caller's
# parameter; test harnesses (hand-written *Exec/*Check/Run_* drivers)
# choose theirs and are outside the scan by design. Runs LAST in the
# suite so that everything generated — including the parity runner's
# P_*.lean modules — is under the scan (pre-merge audit M3).
lean-no-fuel-numerals:
	@echo "=== No fuel numerals in LemLib or generated code (gate) ==="
	@./check_no_fuel_numerals.sh

# reader_consumer compiled behavioral test (effect-retirement L1,
# charter §4.2): consumer call sites must receive the reader value in
# compiled code — lifted-caller injection, HOF partial application,
# and the reader_seed override (elaborator pins live in
# TestReaderConsumerCheck.lean).
lean-reader-consumer:
	@echo "=== reader_consumer injection pin (compiled) ==="
	@cd lean-test && $(LAKE) build test-reader-consumer > /dev/null
	@out=$$(cd lean-test && ./.lake/build/bin/test-reader-consumer 2>&1); st=$$?; \
	if [ $$st -ne 0 ]; then \
		echo "  FAIL (exit $$st):"; echo "$$out"; exit 1; \
	elif ! echo "$$out" | grep -q "reader_consumer: OK"; then \
		echo "  FAIL: no OK line"; echo "$$out"; exit 1; \
	else \
		echo "  OK: compiled consumer injection holds"; \
	fi

# Supply-lifting compiled behavioral test (effect-retirement L1): the
# threaded supply's draw sequences — strict-order numbering, single
# evaluation of destructuring RHSes, fuel/reader/multi-supply
# composition — re-asserted in a real binary (elaborator pins live in
# TestSupplyCheck.lean; compiled-code divergence is exactly the class
# the 2026-08-31 review found untested for effectful).
lean-supply-draws:
	@echo "=== Supply draw-sequence pin (compiled) ==="
	@cd lean-test && $(LAKE) build test-supply-draws > /dev/null
	@out=$$(cd lean-test && ./.lake/build/bin/test-supply-draws 2>&1); st=$$?; \
	if [ $$st -ne 0 ]; then \
		echo "  FAIL (exit $$st):"; echo "$$out"; exit 1; \
	elif ! echo "$$out" | grep -q "supply draws: OK"; then \
		echo "  FAIL: no OK line"; echo "$$out"; exit 1; \
	else \
		echo "  OK: compiled draw sequences hold"; \
	fi

# Non-Lean invariance (effect-retirement charter §6.1/§6.3): the
# '{lean}'-scoped declares in invariance/inv_*.lem must be exact
# no-ops for the semantic emitters — generate each module with and
# without them and byte-compare. Vacuity-guarded: the strip must
# actually remove lines and outputs must exist. (The echoing/human
# targets — lem, ident, tex, html — deliberately re-render declare
# lines; they are covered by the nonlean-regress golden net.)
lean-invariance:
	@echo "=== Non-Lean invariance ({lean} declares are no-ops for ocaml/hol/isa/coq) ==="
	@fail=0; \
	for src in invariance/inv_*.lem; do \
		name=$$(basename $$src); \
		rm -rf invariance/_out; \
		mkdir -p invariance/_out/decl invariance/_out/strip; \
		cp $$src invariance/_out/decl/$$name; \
		grep -v '^declare {lean}' $$src > invariance/_out/strip/$$name; \
		if cmp -s invariance/_out/decl/$$name invariance/_out/strip/$$name; then \
			echo "  FAIL (vacuous): $$name contains no 'declare {lean}' lines"; fail=1; continue; \
		fi; \
		for tgt in ocaml hol isa coq; do \
			(cd invariance/_out/decl && $(CURDIR)/../../lem -wl ign -i $(CURDIR)/../../library/pervasives.lem -$$tgt $$name > /dev/null 2>&1) \
				|| { echo "  FAIL: $$name -$$tgt (declared variant did not generate)"; fail=1; }; \
			(cd invariance/_out/strip && $(CURDIR)/../../lem -wl ign -i $(CURDIR)/../../library/pervasives.lem -$$tgt $$name > /dev/null 2>&1) \
				|| { echo "  FAIL: $$name -$$tgt (stripped variant did not generate)"; fail=1; }; \
		done; \
		rm -f invariance/_out/decl/$$name invariance/_out/strip/$$name; \
		if [ $$(ls invariance/_out/decl | wc -l) -eq 0 ]; then \
			echo "  FAIL (vacuous): $$name produced no non-Lean outputs"; fail=1; continue; \
		fi; \
		if diff -r invariance/_out/decl invariance/_out/strip > /dev/null; then \
			echo "  OK: $$name ($$(ls invariance/_out/decl | wc -l) artifacts byte-identical across ocaml/hol/isa/coq)"; \
		else \
			echo "  FAIL: $$name non-Lean output changed by {lean} declares:"; \
			diff -r invariance/_out/decl invariance/_out/strip | head -10; fail=1; \
		fi; \
	done; \
	rm -rf invariance/_out; exit $$fail

# m7 single-evaluation pin (2026-08-31 backend quality review): a
# multi-name destructuring let's RHS must run ONCE in compiled code —
# the historical per-binding RHS duplication ran effects once per bound
# name (and would silently fork a threaded supply). Compiled-binary
# check: the two counter draws bound by one tuple let must be {1, 2}.
lean-tuple-once:
	@echo "=== m7 single-evaluation pin (tuple-let RHS runs once) ==="
	@cd lean-test && $(LAKE) build test-tuple-let-once > /dev/null
	@out=$$(cd lean-test && ./.lake/build/bin/test-tuple-let-once 2>&1); st=$$?; \
	if [ $$st -ne 0 ]; then \
		echo "  FAIL (exit $$st): $$out"; exit 1; \
	elif ! echo "$$out" | grep -q "single-evaluation: OK"; then \
		echo "  FAIL: no OK line"; echo "$$out"; exit 1; \
	else \
		echo "  OK: $$out"; \
	fi

# Panic-path pin (arc-8 audit fix, auditor A F1): head_undef's
# incomplete-match arm must be a failwithI RAISE carrying the
# Incomplete Pattern message (mirroring OCaml's `failwith m`), never a
# silent default. Two legs (see TestFailwithThreadingPanic.lean):
#  1. library-call semantics (no env var): the panic PRINTS the
#     Incomplete Pattern message, then CONTINUES with the Inhabited
#     default (`survived:` line). Pre-fix this run printed NOTHING —
#     the message line is the pin of the fix.
#  2. harness discipline (LEAN_ABORT_ON_PANIC=1, cerberus
#     scripts/common.sh): the run must fail-stop (nonzero exit). The
#     abort used to fire at module INIT (closed-term extraction lifted
#     LemLib's failwithI applications to initialisation constants,
#     messages disabled there); the parity-fix slice (2026-09-03) made
#     failwithI/fuelExhaustedWith and their implementations
#     `never_extract`, so the abort now fires at the program point —
#     the message is still asserted on leg 1.
lean-panic:
	@echo "=== Panic-path pin (failwithI raise at the L_undefined arm) ==="
	@cd lean-test && $(LAKE) build test-failwith-panic > /dev/null
	@out=$$(cd lean-test && ./.lake/build/bin/test-failwith-panic 2>&1); st=$$?; \
	if [ $$st -ne 0 ]; then \
		echo "  FAIL (leg 1): nonzero exit $$st without LEAN_ABORT_ON_PANIC"; \
		echo "$$out"; exit 1; \
	elif ! echo "$$out" | grep -q "PANIC"; then \
		echo "  FAIL (leg 1): no PANIC line — the arm degraded to a silent default"; \
		echo "$$out"; exit 1; \
	elif ! echo "$$out" | grep -q "Incomplete Pattern"; then \
		echo "  FAIL (leg 1): panic without the Incomplete Pattern message"; \
		echo "$$out"; exit 1; \
	elif ! echo "$$out" | grep -q "survived:"; then \
		echo "  FAIL (leg 1): no post-panic default (library-call semantics changed)"; \
		echo "$$out"; exit 1; \
	else \
		echo "  OK (leg 1): panic prints the Incomplete Pattern message, then continues with default"; \
	fi
	@out=$$(cd lean-test && LEAN_ABORT_ON_PANIC=1 ./.lake/build/bin/test-failwith-panic 2>&1); st=$$?; \
	if [ $$st -eq 0 ]; then \
		echo "  FAIL (leg 2): exited 0 under LEAN_ABORT_ON_PANIC=1 (no fail-stop)"; \
		echo "$$out"; exit 1; \
	elif echo "$$out" | grep -q "survived:"; then \
		echo "  FAIL (leg 2): execution continued past the panic under LEAN_ABORT_ON_PANIC=1"; \
		echo "$$out"; exit 1; \
	else \
		echo "  OK (leg 2): fail-stops (exit $$st) under LEAN_ABORT_ON_PANIC=1"; \
	fi

# Negative probes: each negative/neg_*.lem MUST be rejected, and with the
# error fragment declared in its first-line "(* EXPECT: ... *)" header —
# a rejection for the wrong reason (e.g. a type error) is a FAIL.
lean-negative:
	@echo "=== Negative probes (must be rejected with the declared error) ==="
	@fail=0; \
	for f in negative/neg_*.lem; do \
		exp=$$(sed -n 's/^(\* EXPECT: \(.*\) \*)$$/\1/p' $$f | head -1); \
		out=$$($(LEM) $(LEMFLAGS) -lean $$f 2>&1); \
		if [ $$? -eq 0 ]; then \
			echo "  FAIL (accepted): $$f"; fail=1; \
		elif ! echo "$$out" | grep -qF "$$exp"; then \
			echo "  FAIL (rejected for the wrong reason): $$f"; \
			echo "$$out" | head -3; fail=1; \
		else \
			echo "  OK (rejected as declared): $$f"; \
		fi; \
	done; exit $$fail

# Generate all .lean files from .lem sources
lean-generate: $(TESTS)
	@echo "=== Generating Lean files ==="
	@pass=0; fail=0; skip=0; \
	for f in $(TESTS); do \
		base=$$(basename $$f .lem); \
		if grep -q "^$$f,lean," expected_failures.txt 2>/dev/null; then \
			echo "  SKIP (expected failure): $$f"; \
			skip=$$((skip + 1)); \
		else \
			if $(LEM) $(LEMFLAGS) -lean $$f > /dev/null 2>&1; then \
				echo "  OK: $$f"; \
				pass=$$((pass + 1)); \
			else \
				echo "  FAIL: $$f"; \
				$(LEM) $(LEMFLAGS) -lean $$f 2>&1 | head -5; \
				fail=$$((fail + 1)); \
			fi; \
		fi; \
	done; \
	echo "=== Generation: $$pass passed, $$fail failed, $$skip skipped ==="
	@# Multi-file tests: files that must be compiled together (like Cerberus)
	@# so that lean_mutual_records accumulates across files.
	@if $(LEM) $(LEMFLAGS) -lean test_cross_recup_base.lem test_cross_recup_import.lem > /dev/null 2>&1; then \
		echo "  OK: test_cross_recup_base.lem + test_cross_recup_import.lem (joint)"; \
	else \
		echo "  FAIL: test_cross_recup_base.lem + test_cross_recup_import.lem (joint)"; \
	fi
	@if $(LEM) $(LEMFLAGS) -lean test_cross_field_access.lem test_cross_field_access_import.lem > /dev/null 2>&1; then \
		echo "  OK: test_cross_field_access.lem + test_cross_field_access_import.lem (joint)"; \
	else \
		echo "  FAIL: test_cross_field_access.lem + test_cross_field_access_import.lem (joint)"; \
	fi

# Symlink generated files into lean-test/ and compile with Lake
lean-compile: check-capped
	@echo "=== Compiling Lean files ==="
	@for f in Test_*.lean *_auxiliary.lean; do \
		if [ -f "$$f" ] && [ ! -e "lean-test/$$f" ]; then \
			ln -sf "../$$f" "lean-test/$$f"; \
		fi; \
	done
	@cd lean-test && $(LAKE) build

clean:
	rm -f *.lean *_ok
	@# generated files are SYMLINKED into lean-test/ (lean-compile); remove only
	@# symlinks — a hand-written module whose name follows a generated one
	@# (Test_<x>_lemMeasureProofs.lean, fuel-measure slice) must survive clean
	find lean-test -maxdepth 1 -type l \( -name "Test_*.lean" -o -name "*_auxiliary.lean" \) -delete
	rm -rf lean-test/.lake lean-test/build
