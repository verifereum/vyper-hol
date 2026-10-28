Theory vyperTest_functional_codegen_calling_convention_test_external_contract_calls[no_sig_docs]
Ancestors vyperTestDefs_functional_codegen_calling_convention_test_external_contract_calls
Libs vyperTestRunnerLib
(* Independent batch: global test indices 0..99 of 221.
   CI discovers every vyperTest_*Script.sml; do not import sibling batches.
   Former whole-file replay:
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs_functional_codegen_calling_convention_test_external_contract_calls";
*)
val () = run_tests_on_traces $ all_traces "vyperTestDefs_functional_codegen_calling_convention_test_external_contract_calls";
