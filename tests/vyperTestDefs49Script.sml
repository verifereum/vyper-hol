open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs49";
val () = make_definitions_for_file (49, "../../vyper/tests/export/functional/codegen/features/test_assert_unreachable.json");
val () = export_theory_no_docs();
