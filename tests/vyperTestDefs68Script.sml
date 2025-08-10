open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs68";
val () = make_definitions_for_file (68, "../../vyper/tests/export/functional/codegen/features/test_selfdestruct.json");
val () = export_theory_no_docs();
