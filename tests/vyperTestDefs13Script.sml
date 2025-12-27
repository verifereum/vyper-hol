open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs13";
val () = make_definitions_for_file (13, "vyper-test-exports/functional/codegen/environment_variables/test_blockhash.json");
val () = export_theory_no_docs();
