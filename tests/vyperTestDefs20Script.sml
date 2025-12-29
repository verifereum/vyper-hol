open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs20";
val () = make_definitions_for_file (20, "vyper-test-exports/functional/codegen/modules/test_module_variables.json");
val () = export_theory_no_docs();
