Theory vyperTestDefs_functional_codegen_features_test_clampers[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/features/test_clampers.json", "../vyper-test-exports/functional/codegen/features/test_clampers.json.provenance"];
(* Independent batch: global test indices 0..99 of 739.
   Former whole-file invocation (replaced by bounded batches):
val () = make_definitions_for_file ("functional_codegen_features_test_clampers", "../vyper-test-exports/functional/codegen/features/test_clampers.json");
*)
val () = make_definitions_for_partition ("functional_codegen_features_test_clampers", "../vyper-test-exports/functional/codegen/features/test_clampers.json", 0, 100, 739);
