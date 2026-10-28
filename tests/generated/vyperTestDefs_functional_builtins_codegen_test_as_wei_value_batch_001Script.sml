Theory vyperTestDefs_functional_builtins_codegen_test_as_wei_value_batch_001[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/builtins/codegen/test_as_wei_value.json", "../vyper-test-exports/functional/builtins/codegen/test_as_wei_value.json.provenance"];
(* Independent batch: global test indices 100..103 of 104.
   Former whole-file invocation (replaced by bounded batches):
val () = make_definitions_for_file ("functional_builtins_codegen_test_as_wei_value", "../vyper-test-exports/functional/builtins/codegen/test_as_wei_value.json");
*)
val () = make_definitions_for_partition ("functional_builtins_codegen_test_as_wei_value", "../vyper-test-exports/functional/builtins/codegen/test_as_wei_value.json", 100, 4, 104);
