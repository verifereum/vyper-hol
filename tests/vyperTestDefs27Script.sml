open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs27";
val () = make_definitions_for_file (27, "../../vyper/tests/export/functional/codegen/storage_variables/test_setters.json");
val () = export_theory_no_docs();
