Theory vyperTestDefs_functional_builtins_codegen_test_minmax_value[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/builtins/codegen/test_minmax_value.json", "../vyper-test-exports/functional/builtins/codegen/test_minmax_value.json.provenance"];
(* Independent batch: global test indices 0..99 of 130.
   Former whole-file invocation (replaced by bounded batches):
val () = make_definitions_for_file ("functional_builtins_codegen_test_minmax_value", "../vyper-test-exports/functional/builtins/codegen/test_minmax_value.json");
*)
val () = make_definitions_for_partition ("functional_builtins_codegen_test_minmax_value", "../vyper-test-exports/functional/builtins/codegen/test_minmax_value.json", 0, 100, 130);
