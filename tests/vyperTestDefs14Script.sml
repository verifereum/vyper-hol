open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs14";
val () = make_definitions_for_file (14, "vyper-test-exports/functional/codegen/environment_variables/test_tx.json");
val () = export_theory_no_docs();
