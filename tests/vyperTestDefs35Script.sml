open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs35";
val () = make_definitions_for_file (35, "../../vyper/tests/export/functional/codegen/types/numbers/test_signed_ints.json");
val () = export_theory_no_docs();
