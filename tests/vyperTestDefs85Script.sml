open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs85";
val () = make_definitions_for_file (85, "vyper-test-exports/functional/codegen/features/iteration/test_for_range.json");
val () = export_theory_no_docs();
