Theory vyperTestDefs_functional_codegen_test_interfaces[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/test_interfaces.json"];
val () = make_definitions_for_file ("functional_codegen_test_interfaces", "../vyper-test-exports/functional/codegen/test_interfaces.json");
