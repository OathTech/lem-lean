LEM = ../../lem
LEMLIB = ../../library
LEMFLAGS = -wl ign -i $(LEMLIB)/pervasives.lem

TESTS = $(sort $(wildcard test_*.lem))

.PHONY: all lean lean-generate lean-compile clean

all: lean

# === Lean Backend ===

lean: lean-generate lean-compile lean-negative

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
