open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs43";
val () = make_definitions_for_file (43, "../../vyper/tests/export/functional/codegen/types/test_lists.json");
val () = export_theory_no_docs();
