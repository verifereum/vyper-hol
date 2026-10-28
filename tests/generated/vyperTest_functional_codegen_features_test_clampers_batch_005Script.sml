Theory vyperTest_functional_codegen_features_test_clampers_batch_005[no_sig_docs]
Ancestors vyperTestDefs_functional_codegen_features_test_clampers_batch_005
Libs vyperTestRunnerLib
(* Independent batch: global test indices 500..599 of 739.
   CI discovers every vyperTest_*Script.sml; do not import sibling batches.
   Former whole-file replay:
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs_functional_codegen_features_test_clampers";
*)
val () = run_tests_on_traces $ all_traces "vyperTestDefs_functional_codegen_features_test_clampers_batch_005";
