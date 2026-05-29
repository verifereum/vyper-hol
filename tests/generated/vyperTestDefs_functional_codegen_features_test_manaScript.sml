Theory vyperTestDefs_functional_codegen_features_test_mana[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/features/test_mana.json"];
val () = make_definitions_for_file ("functional_codegen_features_test_mana", "../vyper-test-exports/functional/codegen/features/test_mana.json");
