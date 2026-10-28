Theory vyperTest_functional_codegen_features_test_ternary_part_256[no_sig_docs]
Ancestors vyperTestDefs_functional_codegen_features_test_ternary_part_256
Libs vyperTestRunnerLib
val () = if List.length (all_traces "vyperTestDefs_functional_codegen_features_test_ternary_part_256") = 51 then () else raise Fail "incomplete test shard";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs_functional_codegen_features_test_ternary_part_256";
