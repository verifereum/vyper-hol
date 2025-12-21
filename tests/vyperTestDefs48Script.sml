open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs48";
val () = make_definitions_for_file (48, "vyper-test-exports/functional/codegen/features/test_address_balance.json");
val () = export_theory_no_docs();
