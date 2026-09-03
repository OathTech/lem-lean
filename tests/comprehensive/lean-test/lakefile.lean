import Lake
open Lake DSL

package LemComprehensiveTest where
  version := v!"0.1.0"
  moreLeanArgs := #["-DautoImplicit=false"]

require LemLib from "../../../lean-lib"

@[default_target]
lean_lib LemComprehensiveTest where
  srcDir := "."
  roots := #[
    `Test_case_arm_parsing, `Test_case_arm_parsing_auxiliary,
    `Test_cerberus_patterns, `Test_cerberus_patterns_auxiliary,
    `Test_classes, `Test_classes_auxiliary,
    `Test_collections, `Test_collections_auxiliary,
    `Test_contextual_keywords, `Test_contextual_keywords_auxiliary,
    `Test_cross_field_access,
    `Test_cross_field_access_import,
    `Test_cross_module, `Test_cross_module_auxiliary,
    `Test_cross_module_base, `Test_cross_module_base_auxiliary,
    `Test_cross_module_import, `Test_cross_module_import_auxiliary,
    `Test_cross_recup_base, `Test_cross_recup_base_auxiliary,
    `Test_cross_recup_import, `Test_cross_recup_import_auxiliary,
    `Test_derived_comparison, `Test_derived_comparison_auxiliary,
    `Test_derived_inhabited, `Test_derived_inhabited_auxiliary,
    `TestDerivedInhabitedCheck,  -- hand-written arc-8 S1 instance-shape checks
    `TestInstancePriorityCheck,  -- hand-written arc-14 B4 resolution probe (be:G1/sem:S2)
    `TestNameCaptureCheck,  -- arc-14 re-mark be:S1 none-binder pin
    `Test_deriving, `Test_deriving_auxiliary,
    `Test_either_maybe, `Test_either_maybe_auxiliary,
    `Test_expressions, `Test_expressions_auxiliary,
    `Test_integer_div, `Test_integer_div_auxiliary,
    `Test_instance_priority, `Test_instance_priority_auxiliary,
    `Test_name_capture, `Test_name_capture_auxiliary,
    `Test_failwith_threading, `Test_failwith_threading_auxiliary,
    `TestFailwithThreadingCheck,  -- hand-written arc-8 S2 signature-shape checks
    `Test_fuel_budget, `Test_fuel_budget_auxiliary,
    `Test_functions, `Test_functions_auxiliary,
    `Test_indreln, `Test_indreln_auxiliary,
    `Test_instances, `Test_instances_auxiliary,
    `Test_keywords, `Test_keywords_auxiliary,
    `Test_let_bindings, `Test_let_bindings_auxiliary,
    `Test_misc, `Test_misc_auxiliary,
    `Test_modules, `Test_modules_auxiliary,
    `Test_mutual_types, `Test_mutual_types_auxiliary,
    `Test_mword, `Test_mword_auxiliary,
    `Test_numeric, `Test_numeric_auxiliary,
    `Test_patterns, `Test_patterns_auxiliary,
    `Test_reader_consumer, `Test_reader_consumer_auxiliary,
    `TestReaderConsumerImpl,   -- hand-written consumer implementation (leading reader params)
    `TestReaderConsumerCheck,  -- hand-written reader_consumer pins (effect-retirement L1)
    `Test_records, `Test_records_auxiliary,
    `Test_scope_shadowing, `Test_scope_shadowing_auxiliary,
    `Test_strings_chars, `Test_strings_chars_auxiliary,
    `Test_target_reps, `Test_target_reps_auxiliary,
    `Test_target_specific, `Test_target_specific_auxiliary,
    `Test_termination, `Test_termination_auxiliary,
    `Test_stress, `Test_stress_auxiliary,
    `Test_supply, `Test_supply_auxiliary,
    `Test_supply_multi, `Test_supply_multi_auxiliary,
    `TestSupplyCheck,  -- hand-written supply draw-order/signature pins (effect-retirement L1)
    `Test_types_advanced, `Test_types_advanced_auxiliary,
    `Test_tuple_let_once, `Test_tuple_let_once_auxiliary,
    `TupleLetTick,  -- hand-written m7 single-evaluation counter
    `Test_types_basic, `Test_types_basic_auxiliary,
    `Test_vectors, `Test_vectors_auxiliary,
    `TestExtraImportHelper  -- hand-written helper for extra_import test
  ]

-- Arc-8 audit fix (auditor A F1): panic-path pin for the L_undefined
-- rendering (run by the Makefile `lean-panic` target under
-- LEAN_ABORT_ON_PANIC=1; must abort with the Incomplete Pattern message).
lean_exe «test-failwith-panic» where
  root := `TestFailwithThreadingPanic

lean_exe «test-tuple-let-once» where
  root := `TestTupleLetOnce

-- Effect-retirement L1: compiled-binary behavioral test of the supply
-- transform (draw sequencing, single evaluation, fuel/reader/multi
-- composition; suite phase lean-supply-draws).
lean_exe «test-supply-draws» where
  root := `TestSupplyDraws

-- Effect-retirement L1: compiled-binary behavioral test of
-- reader_consumer injection (lifted caller, HOF partial application,
-- reader_seed pickup; suite phase lean-reader-consumer).
lean_exe «test-reader-consumer» where
  root := `TestReaderConsumerExec

-- Effect-retirement L1: compiled-binary behavioral test of
-- per-declaration fuel budgets (budgeted cut at N, unannotated
-- sibling at the exact lemDefaultFuel boundary, reader composition;
-- suite phase lean-fuel-budget).
lean_exe «test-fuel-budget» where
  root := `TestFuelBudgetExec
