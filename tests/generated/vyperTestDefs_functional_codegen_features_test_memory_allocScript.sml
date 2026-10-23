Theory vyperTestDefs_functional_codegen_features_test_memory_alloc[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/features/test_memory_alloc.json"];
val () = make_definitions_for_file ("functional_codegen_features_test_memory_alloc", "../vyper-test-exports/functional/codegen/features/test_memory_alloc.json");
