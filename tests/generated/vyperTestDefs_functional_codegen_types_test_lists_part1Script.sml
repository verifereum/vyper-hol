Theory vyperTestDefs_functional_codegen_types_test_lists_part1[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/types/test_lists.json", "../vyper-test-exports/functional/codegen/types/test_lists.json.provenance"];
val () = make_definitions_for_file_range ("functional_codegen_types_test_lists", "../vyper-test-exports/functional/codegen/types/test_lists.json", 21, 1);
