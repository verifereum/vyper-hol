Theory vyperTestDefs_functional_codegen_features_test_short_circuiting_part1[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/features/test_short_circuiting.json", "../vyper-test-exports/functional/codegen/features/test_short_circuiting.json.provenance"];
val () = make_definitions_for_file_range ("functional_codegen_features_test_short_circuiting", "../vyper-test-exports/functional/codegen/features/test_short_circuiting.json", 100, 56);
