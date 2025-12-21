open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs82";
val () = make_definitions_for_file (82, "vyper-test-exports/functional/codegen/features/iteration/test_break.json");
val () = export_theory_no_docs();
