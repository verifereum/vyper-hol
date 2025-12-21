open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs53";
val () = make_definitions_for_file (53, "vyper-test-exports/functional/codegen/features/test_clampers.json");
val () = export_theory_no_docs();
