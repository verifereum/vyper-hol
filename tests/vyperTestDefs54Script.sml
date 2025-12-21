open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs54";
val () = make_definitions_for_file (54, "vyper-test-exports/functional/codegen/features/test_comments.json");
val () = export_theory_no_docs();
