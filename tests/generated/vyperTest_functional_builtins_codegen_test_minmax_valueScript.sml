Theory vyperTest_functional_builtins_codegen_test_minmax_value[no_sig_docs]
Ancestors vyperTestDefs_functional_builtins_codegen_test_minmax_value
Libs vyperTestRunnerLib
(* Independent batch: global test indices 0..99 of 130.
   CI discovers every vyperTest_*Script.sml; do not import sibling batches.
   Former whole-file replay:
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs_functional_builtins_codegen_test_minmax_value";
*)
val () = run_tests_on_traces $ all_traces "vyperTestDefs_functional_builtins_codegen_test_minmax_value";
