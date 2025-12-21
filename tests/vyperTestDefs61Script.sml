open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs61";
val () = make_definitions_for_file (61, "vyper-test-exports/functional/codegen/features/test_init.json");
val () = export_theory_no_docs();
