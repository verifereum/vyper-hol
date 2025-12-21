open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs69";
val () = make_definitions_for_file (69, "vyper-test-exports/functional/codegen/features/test_reverting.json");
val () = export_theory_no_docs();
