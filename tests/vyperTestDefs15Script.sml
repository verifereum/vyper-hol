open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs15";
val () = make_definitions_for_file (15, "vyper-test-exports/functional/codegen/modules/test_events.json");
val () = export_theory_no_docs();
