open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs60";
val () = make_definitions_for_file (60, "vyper-test-exports/functional/codegen/features/test_immutable.json");
val () = export_theory_no_docs();
