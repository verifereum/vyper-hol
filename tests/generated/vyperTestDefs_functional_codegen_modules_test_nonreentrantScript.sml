Theory vyperTestDefs_functional_codegen_modules_test_nonreentrant[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/modules/test_nonreentrant.json"];
val () = make_definitions_for_file ("functional_codegen_modules_test_nonreentrant", "../vyper-test-exports/functional/codegen/modules/test_nonreentrant.json");
