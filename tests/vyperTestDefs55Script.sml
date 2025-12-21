open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs55";
val () = make_definitions_for_file (55, "vyper-test-exports/functional/codegen/features/test_comparison.json");
val () = export_theory_no_docs();
