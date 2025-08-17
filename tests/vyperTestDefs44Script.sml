open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs44";
val () = make_definitions_for_file (44, "../../vyper/tests/export/functional/codegen/types/test_node_types.json");
val () = export_theory_no_docs();
