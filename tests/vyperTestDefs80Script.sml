open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs80";
val () = make_definitions_for_file (80, "../../vyper/tests/export/functional/codegen/features/decorators/test_view.json");
val () = export_theory_no_docs();
