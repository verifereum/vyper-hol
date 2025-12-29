open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs47";
val () = make_definitions_for_file (47, "vyper-test-exports/functional/codegen/types/test_struct.json");
val () = export_theory_no_docs();
