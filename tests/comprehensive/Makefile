LEM = ../../lem
LEMLIB = ../../library
LEMFLAGS = -wl ign -i $(LEMLIB)/pervasives.lem

TESTS = $(sort $(wildcard test_*.lem))

.PHONY: all lean lean-generate lean-compile lean-negative lean-panic clean

all: lean

# === Lean Backend ===

lean: lean-generate lean-compile lean-panic lean-negative

# Panic-path pin (arc-8 audit fix, auditor A F1): head_undef's
# incomplete-match arm must be a failwithI RAISE carrying the
# Incomplete Pattern message (mirroring OCaml's `failwith m`), never a
# silent default. Two legs (see TestFailwithThreadingPanic.lean):
#  1. library-call semantics (no env var): the panic PRINTS the
#     Incomplete Pattern message, then CONTINUES with the Inhabited
#     default (`survived:` line). Pre-fix this run printed NOTHING —
#     the message line is the pin of the fix.
#  2. harness discipline (LEAN_ABORT_ON_PANIC=1, cerberus
#     scripts/common.sh): the run must fail-stop (nonzero exit). On
#     this 4.28 toolchain the abort fires at module INIT (LemLib's own
#     eager closed-term failwithI lifts, messages disabled there), so
#     the message is asserted on leg 1, not this leg.
lean-panic:
	@echo "=== Panic-path pin (failwithI raise at the L_undefined arm) ==="
	@cd lean-test && lake build test-failwith-panic > /dev/null
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
lean-compile:
	@echo "=== Compiling Lean files ==="
	@for f in Test_*.lean *_auxiliary.lean; do \
		if [ -f "$$f" ] && [ ! -e "lean-test/$$f" ]; then \
			ln -sf "../$$f" "lean-test/$$f"; \
		fi; \
	done
	@cd lean-test && lake build

clean:
	rm -f *.lean *_ok
	rm -f lean-test/Test_*.lean lean-test/*_auxiliary.lean
	rm -rf lean-test/.lake lean-test/build
