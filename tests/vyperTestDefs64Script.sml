open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs64";
val () = make_definitions_for_file (64, "vyper-test-exports/functional/codegen/features/test_logging_from_call.json");
val () = export_theory_no_docs();
