open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs86";
val () = make_definitions_for_file (86, "../../vyper/tests/export/functional/codegen/features/iteration/test_range_in.json");
val () = export_theory_no_docs();
