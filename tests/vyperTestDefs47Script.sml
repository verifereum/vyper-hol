open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs47";
val () = make_definitions_for_file (47, "../../vyper/tests/export/functional/codegen/features/test_address_balance.json");
val () = export_theory_no_docs();
