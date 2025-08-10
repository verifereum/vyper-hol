open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs52";
val () = make_definitions_for_file (52, "../../vyper/tests/export/functional/codegen/features/test_comments.json");
val () = export_theory_no_docs();
