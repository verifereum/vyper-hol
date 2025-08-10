open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs82";
val () = make_definitions_for_file (82, "../../vyper/tests/export/functional/codegen/features/iteration/test_continue.json");
val () = export_theory_no_docs();
