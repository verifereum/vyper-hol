open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs85";
val () = make_definitions_for_file (85, "../../vyper/tests/export/functional/codegen/features/iteration/test_for_range.json");
val () = export_theory_no_docs();
