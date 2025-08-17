open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs28";
val () = make_definitions_for_file (28, "../../vyper/tests/export/functional/codegen/storage_variables/test_storage_variable.json");
val () = export_theory_no_docs();
