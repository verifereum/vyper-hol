Theory vyperTest_functional_builtins_codegen_test_as_wei_value_part_64[no_sig_docs]
Ancestors vyperTestDefs_functional_builtins_codegen_test_as_wei_value_part_64
Libs vyperTestRunnerLib
val () = if List.length (all_traces "vyperTestDefs_functional_builtins_codegen_test_as_wei_value_part_64") = 40 then () else raise Fail "incomplete test shard";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs_functional_builtins_codegen_test_as_wei_value_part_64";
