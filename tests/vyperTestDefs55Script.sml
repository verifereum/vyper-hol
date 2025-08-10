open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs55";
val () = make_definitions_for_file (55, "../../vyper/tests/export/functional/codegen/features/test_constructor.json");
val () = export_theory_no_docs();
