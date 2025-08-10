open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs18";
val () = make_definitions_for_file (18, "../../vyper/tests/export/functional/codegen/modules/test_module_constants.json");
val () = export_theory_no_docs();
