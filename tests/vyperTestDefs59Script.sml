open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs59";
val () = make_definitions_for_file (59, "../../vyper/tests/export/functional/codegen/features/test_immutable.json");
val () = export_theory_no_docs();
