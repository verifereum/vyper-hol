open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs75";
val () = make_definitions_for_file (75, "vyper-test-exports/functional/codegen/features/decorators/test_nonreentrant.json");
val () = export_theory_no_docs();
