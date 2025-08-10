open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs14";
val () = make_definitions_for_file (14, "../../vyper/tests/export/functional/codegen/modules/test_events.json");
val () = export_theory_no_docs();
