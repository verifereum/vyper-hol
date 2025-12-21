open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs49";
val () = make_definitions_for_file (49, "vyper-test-exports/functional/codegen/features/test_assert.json");
val () = export_theory_no_docs();
