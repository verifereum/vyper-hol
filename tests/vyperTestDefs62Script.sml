open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs62";
val () = make_definitions_for_file (62, "vyper-test-exports/functional/codegen/features/test_logging.json");
val () = export_theory_no_docs();
