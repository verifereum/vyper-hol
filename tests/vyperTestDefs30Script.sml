open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs30";
val () = make_definitions_for_file (30, "../../vyper/tests/export/functional/codegen/types/numbers/test_division.json");
val () = export_theory_no_docs();
