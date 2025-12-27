open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs10";
val () = make_definitions_for_file (10, "vyper-test-exports/functional/codegen/calling_convention/test_self_call_struct.json");
val () = export_theory_no_docs();
