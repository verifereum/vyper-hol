Theory vyperTestDefs_functional_codegen_types_numbers_test_unsigned_ints_batch_001[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/types/numbers/test_unsigned_ints.json", "../vyper-test-exports/functional/codegen/types/numbers/test_unsigned_ints.json.provenance"];
(* Independent batch: global test indices 100..159 of 160.
   Former whole-file invocation (replaced by bounded batches):
val () = make_definitions_for_file ("functional_codegen_types_numbers_test_unsigned_ints", "../vyper-test-exports/functional/codegen/types/numbers/test_unsigned_ints.json");
*)
val () = make_definitions_for_partition ("functional_codegen_types_numbers_test_unsigned_ints", "../vyper-test-exports/functional/codegen/types/numbers/test_unsigned_ints.json", 100, 60, 160);
