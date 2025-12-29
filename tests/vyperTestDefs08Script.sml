open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs08";
val () = make_definitions_for_file (8, "vyper-test-exports/functional/codegen/calling_convention/test_new_call_convention.json");
val () = export_theory_no_docs();
