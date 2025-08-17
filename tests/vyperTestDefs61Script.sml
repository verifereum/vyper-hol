open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs61";
val () = make_definitions_for_file (61, "../../vyper/tests/export/functional/codegen/features/test_init.json");
val () = export_theory_no_docs();
