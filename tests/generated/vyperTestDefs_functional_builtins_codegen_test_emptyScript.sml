Theory vyperTestDefs_functional_builtins_codegen_test_empty[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/builtins/codegen/test_empty.json"];
val () = make_definitions_for_file ("functional_builtins_codegen_test_empty", "../vyper-test-exports/functional/builtins/codegen/test_empty.json");
