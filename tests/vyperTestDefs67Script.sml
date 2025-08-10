open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs67";
val () = make_definitions_for_file (67, "../../vyper/tests/export/functional/codegen/features/test_packing.json");
val () = export_theory_no_docs();
