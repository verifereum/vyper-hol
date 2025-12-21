open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs73";
val () = make_definitions_for_file (73, "vyper-test-exports/functional/codegen/features/test_ternary.json");
val () = export_theory_no_docs();
