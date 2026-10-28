Theory vyperTest_functional_builtins_codegen_test_minmax_value_part_128[no_sig_docs]
Ancestors vyperTestDefs_functional_builtins_codegen_test_minmax_value_part_128
Libs vyperTestRunnerLib
val () = if List.length (all_traces "vyperTestDefs_functional_builtins_codegen_test_minmax_value_part_128") = 2 then () else raise Fail "incomplete test shard";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs_functional_builtins_codegen_test_minmax_value_part_128";
