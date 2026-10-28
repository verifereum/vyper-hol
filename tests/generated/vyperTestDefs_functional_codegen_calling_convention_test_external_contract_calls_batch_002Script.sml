Theory vyperTestDefs_functional_codegen_calling_convention_test_external_contract_calls_batch_002[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/calling_convention/test_external_contract_calls.json", "../vyper-test-exports/functional/codegen/calling_convention/test_external_contract_calls.json.provenance"];
(* Independent batch: global test indices 200..220 of 221.
   Former whole-file invocation (replaced by bounded batches):
val () = make_definitions_for_file ("functional_codegen_calling_convention_test_external_contract_calls", "../vyper-test-exports/functional/codegen/calling_convention/test_external_contract_calls.json");
*)
val () = make_definitions_for_partition ("functional_codegen_calling_convention_test_external_contract_calls", "../vyper-test-exports/functional/codegen/calling_convention/test_external_contract_calls.json", 200, 21, 221);
