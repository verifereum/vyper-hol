open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs02";
val () = make_definitions_for_file (2, "../../vyper/tests/export/functional/codegen/test_selector_table_stability.json");
val () = export_theory_no_docs();
