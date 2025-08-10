open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs69";
val () = make_definitions_for_file (69, "../../vyper/tests/export/functional/codegen/features/test_selfdestruct.json");
val () = export_theory_no_docs();
