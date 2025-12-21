open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs00";
val () = make_definitions_for_file (0, "vyper-test-exports/functional/codegen/test_interfaces.json");
val () = export_theory_no_docs();
