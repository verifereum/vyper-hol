Theory vyperTestDefs_functional_codegen_integration_test_escrow[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/integration/test_escrow.json"];
val () = make_definitions_for_file ("functional_codegen_integration_test_escrow", "../vyper-test-exports/functional/codegen/integration/test_escrow.json");
