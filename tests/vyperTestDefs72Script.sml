open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs72";
val () = make_definitions_for_file (72, "vyper-test-exports/functional/codegen/features/test_string_map_keys.json");
val () = export_theory_no_docs();
