open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs17";
val () = make_definitions_for_file (17, "../../vyper/tests/export/functional/codegen/modules/test_flag_imports.json");
val () = export_theory_no_docs();
