Theory vyperTestDefs_functional_codegen_test_selector_table[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/test_selector_table.json"];
val () = make_definitions_for_file ("functional_codegen_test_selector_table", "../vyper-test-exports/functional/codegen/test_selector_table.json");
