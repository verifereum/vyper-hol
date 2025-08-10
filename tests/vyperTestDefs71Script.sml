open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs71";
val () = make_definitions_for_file (71, "../../vyper/tests/export/functional/codegen/features/test_string_map_keys.json");
val () = export_theory_no_docs();
