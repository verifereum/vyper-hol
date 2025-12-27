open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs52";
val () = make_definitions_for_file (52, "vyper-test-exports/functional/codegen/features/test_bytes_map_keys.json");
val () = export_theory_no_docs();
