open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs40";
val () = make_definitions_for_file (40, "vyper-test-exports/functional/codegen/types/test_dynamic_array.json");
val () = export_theory_no_docs();
