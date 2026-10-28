Theory vyperTest_functional_codegen_types_numbers_test_signed_ints_part_128[no_sig_docs]
Ancestors vyperTestDefs_functional_codegen_types_numbers_test_signed_ints_part_128
Libs vyperTestRunnerLib
val () = if List.length (all_traces "vyperTestDefs_functional_codegen_types_numbers_test_signed_ints_part_128") = 64 then () else raise Fail "incomplete test shard";
val () = List.app run_test_on_traces $ all_traces "vyperTestDefs_functional_codegen_types_numbers_test_signed_ints_part_128";
