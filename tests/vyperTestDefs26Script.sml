open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs26";
val () = make_definitions_for_file (26, "../../vyper/tests/export/functional/codegen/storage_variables/test_setters.json");
val () = export_theory_no_docs();
