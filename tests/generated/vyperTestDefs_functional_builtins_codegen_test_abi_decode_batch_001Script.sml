Theory vyperTestDefs_functional_builtins_codegen_test_abi_decode_batch_001[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/builtins/codegen/test_abi_decode.json", "../vyper-test-exports/functional/builtins/codegen/test_abi_decode.json.provenance"];
(* Independent batch: global test indices 100..115 of 116.
   Former whole-file invocation (replaced by bounded batches):
val () = make_definitions_for_file ("functional_builtins_codegen_test_abi_decode", "../vyper-test-exports/functional/builtins/codegen/test_abi_decode.json");
*)
val () = make_definitions_for_partition ("functional_builtins_codegen_test_abi_decode", "../vyper-test-exports/functional/builtins/codegen/test_abi_decode.json", 100, 16, 116);
