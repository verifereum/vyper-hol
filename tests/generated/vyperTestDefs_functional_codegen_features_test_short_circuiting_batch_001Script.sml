Theory vyperTestDefs_functional_codegen_features_test_short_circuiting_batch_001[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/features/test_short_circuiting.json", "../vyper-test-exports/functional/codegen/features/test_short_circuiting.json.provenance"];
(* Independent batch: global test indices 100..155 of 156.
   Former whole-file invocation (replaced by bounded batches):
val () = make_definitions_for_file ("functional_codegen_features_test_short_circuiting", "../vyper-test-exports/functional/codegen/features/test_short_circuiting.json");
*)
val () = make_definitions_for_partition ("functional_codegen_features_test_short_circuiting", "../vyper-test-exports/functional/codegen/features/test_short_circuiting.json", 100, 56, 156);
