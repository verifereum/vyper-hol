open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs30";
val () = make_definitions_for_file (30, "vyper-test-exports/functional/codegen/types/numbers/test_decimals.json");
val () = export_theory_no_docs();
