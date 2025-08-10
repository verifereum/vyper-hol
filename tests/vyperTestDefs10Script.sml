open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs10";
val () = make_definitions_for_file (10, "../../vyper/tests/export/functional/codegen/environment_variables/test_blobbasefee.json");
val () = export_theory_no_docs();
