open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs59";
val () = make_definitions_for_file (59, "vyper-test-exports/functional/codegen/features/test_gas.json");
val () = export_theory_no_docs();
