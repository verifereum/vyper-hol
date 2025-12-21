open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs01";
val () = make_definitions_for_file (1, "vyper-test-exports/functional/codegen/test_selector_table.json");
val () = export_theory_no_docs();
