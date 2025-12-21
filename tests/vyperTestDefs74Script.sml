open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs74";
val () = make_definitions_for_file (74, "vyper-test-exports/functional/codegen/features/test_transient.json");
val () = export_theory_no_docs();
