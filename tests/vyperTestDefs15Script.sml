open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs15";
val () = make_definitions_for_file (15, "../../vyper/tests/export/functional/codegen/modules/test_exports.json");
val () = export_theory_no_docs();
