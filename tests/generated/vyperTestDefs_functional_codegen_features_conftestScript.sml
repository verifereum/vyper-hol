Theory vyperTestDefs_functional_codegen_features_conftest[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/features/conftest.json", "../vyper-test-exports/functional/codegen/features/conftest.json.provenance"];
val () = make_definitions_for_file ("functional_codegen_features_conftest", "../vyper-test-exports/functional/codegen/features/conftest.json");
