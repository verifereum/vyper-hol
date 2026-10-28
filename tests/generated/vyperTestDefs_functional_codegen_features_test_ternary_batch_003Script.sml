Theory vyperTestDefs_functional_codegen_features_test_ternary_batch_003[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/features/test_ternary.json", "../vyper-test-exports/functional/codegen/features/test_ternary.json.provenance"];
(* Independent batch: global test indices 300..306 of 307.
   Former whole-file invocation (replaced by bounded batches):
val () = make_definitions_for_file ("functional_codegen_features_test_ternary", "../vyper-test-exports/functional/codegen/features/test_ternary.json");
*)
val () = make_definitions_for_partition ("functional_codegen_features_test_ternary", "../vyper-test-exports/functional/codegen/features/test_ternary.json", 300, 7, 307);
