open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs84";
val () = make_definitions_for_file (84, "vyper-test-exports/functional/codegen/features/iteration/test_for_in_list.json");
val () = export_theory_no_docs();
