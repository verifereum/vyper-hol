open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs60";
val () = make_definitions_for_file (60, "../../vyper/tests/export/functional/codegen/features/test_init.json");
val () = export_theory_no_docs();
