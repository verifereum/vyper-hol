open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs63";
val () = make_definitions_for_file (63, "../../vyper/tests/export/functional/codegen/features/test_logging_from_call.json");
val () = export_theory_no_docs();
