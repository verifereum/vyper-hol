open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs62";
val () = make_definitions_for_file (62, "../../vyper/tests/export/functional/codegen/features/test_logging.json");
val () = export_theory_no_docs();
