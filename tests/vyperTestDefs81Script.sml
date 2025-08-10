open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs81";
val () = make_definitions_for_file (81, "../../vyper/tests/export/functional/codegen/features/iteration/test_continue.json");
val () = export_theory_no_docs();
