Theory vyperTest_functional_builtins_codegen_test_as_wei_value_batch_001[no_sig_docs]
Ancestors vyperTestDefs_functional_builtins_codegen_test_as_wei_value_batch_001
Libs vyperTestRunnerLib
(* Independent batch: global test indices 100..103 of 104.
   CI discovers every vyperTest_*Script.sml; do not import sibling batches.
   Former whole-file replay:
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs_functional_builtins_codegen_test_as_wei_value";
*)
val () = run_tests_on_traces $ all_traces "vyperTestDefs_functional_builtins_codegen_test_as_wei_value_batch_001";
