Theory vyperTestDefs_functional_codegen_features_iteration_test_for_range_batch_001[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/features/iteration/test_for_range.json", "../vyper-test-exports/functional/codegen/features/iteration/test_for_range.json.provenance"];
(* Independent batch: global test indices 100..146 of 147.
   Former whole-file invocation (replaced by bounded batches):
val () = make_definitions_for_file ("functional_codegen_features_iteration_test_for_range", "../vyper-test-exports/functional/codegen/features/iteration/test_for_range.json");
*)
val () = make_definitions_for_partition ("functional_codegen_features_iteration_test_for_range", "../vyper-test-exports/functional/codegen/features/iteration/test_for_range.json", 100, 47, 147);
