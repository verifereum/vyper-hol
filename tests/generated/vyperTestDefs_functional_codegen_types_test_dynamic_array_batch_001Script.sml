Theory vyperTestDefs_functional_codegen_types_test_dynamic_array_batch_001[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/types/test_dynamic_array.json", "../vyper-test-exports/functional/codegen/types/test_dynamic_array.json.provenance"];
(* Independent batch: global test indices 100..173 of 174.
   Former whole-file invocation (replaced by bounded batches):
val () = make_definitions_for_file ("functional_codegen_types_test_dynamic_array", "../vyper-test-exports/functional/codegen/types/test_dynamic_array.json");
*)
val () = make_definitions_for_partition ("functional_codegen_types_test_dynamic_array", "../vyper-test-exports/functional/codegen/types/test_dynamic_array.json", 100, 74, 174);
