open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs21";
val () = make_definitions_for_file (21, "../../vyper/tests/export/functional/codegen/modules/test_stateless_functions.json");
val () = export_theory_no_docs();
