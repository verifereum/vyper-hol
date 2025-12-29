open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs06";
val () = make_definitions_for_file (6, "vyper-test-exports/functional/codegen/calling_convention/test_internal_call.json");
val () = export_theory_no_docs();
