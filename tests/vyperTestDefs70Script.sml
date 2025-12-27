open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs70";
val () = make_definitions_for_file (70, "vyper-test-exports/functional/codegen/features/test_selfdestruct.json");
val () = export_theory_no_docs();
