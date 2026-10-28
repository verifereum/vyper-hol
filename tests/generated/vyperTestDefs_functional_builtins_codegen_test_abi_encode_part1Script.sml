Theory vyperTestDefs_functional_builtins_codegen_test_abi_encode_part1[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/builtins/codegen/test_abi_encode.json", "../vyper-test-exports/functional/builtins/codegen/test_abi_encode.json.provenance"];
val () = make_definitions_for_file_range ("functional_builtins_codegen_test_abi_encode", "../vyper-test-exports/functional/builtins/codegen/test_abi_encode.json", 8, 4);
