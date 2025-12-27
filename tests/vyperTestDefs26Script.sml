open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs26";
val () = make_definitions_for_file (26, "vyper-test-exports/functional/codegen/storage_variables/test_getters.json");
val () = export_theory_no_docs();
