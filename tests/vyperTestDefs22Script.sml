open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs22";
val () = make_definitions_for_file (22, "vyper-test-exports/functional/codegen/modules/test_stateless_functions.json");
val () = export_theory_no_docs();
