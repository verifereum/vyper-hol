Theory vyperTest_functional_codegen_types_numbers_test_signed_ints_batch_001[no_sig_docs]
Ancestors vyperTestDefs_functional_codegen_types_numbers_test_signed_ints_batch_001
Libs vyperTestRunnerLib
(* Independent batch: global test indices 100..199 of 206.
   CI discovers every vyperTest_*Script.sml; do not import sibling batches.
   Former whole-file replay:
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs_functional_codegen_types_numbers_test_signed_ints";
*)
val () = run_tests_on_traces $ all_traces "vyperTestDefs_functional_codegen_types_numbers_test_signed_ints_batch_001";
