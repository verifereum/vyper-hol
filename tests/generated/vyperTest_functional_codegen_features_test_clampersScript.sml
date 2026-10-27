Theory vyperTest_functional_codegen_features_test_clampers[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib vyperTestRunnerLib

(* Keep data generation and execution together: importing this very wide
   definitions theory consumes excessive memory before any test can run. *)
val () = holbuild_extra_deps
  ["../vyper-test-exports/functional/codegen/features/test_clampers.json",
   "../vyper-test-exports/functional/codegen/features/test_clampers.json.provenance"];
val () = make_definitions_for_file
  ("functional_codegen_features_test_clampers",
   "../vyper-test-exports/functional/codegen/features/test_clampers.json");
val () = List.app run_test_on_traces $
  all_traces "vyperTest_functional_codegen_features_test_clampers";
