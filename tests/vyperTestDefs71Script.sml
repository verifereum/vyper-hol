open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs71";
val () = make_definitions_for_file (71, "vyper-test-exports/functional/codegen/features/test_short_circuiting.json");
val () = export_theory_no_docs();
