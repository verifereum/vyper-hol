open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs51";
val () = make_definitions_for_file (51, "vyper-test-exports/functional/codegen/features/test_assignment.json");
val () = export_theory_no_docs();
