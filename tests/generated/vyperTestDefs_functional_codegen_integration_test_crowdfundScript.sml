Theory vyperTestDefs_functional_codegen_integration_test_crowdfund[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/integration/test_crowdfund.json"];
val () = make_definitions_for_file ("functional_codegen_integration_test_crowdfund", "../vyper-test-exports/functional/codegen/integration/test_crowdfund.json");
