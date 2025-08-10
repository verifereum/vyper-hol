open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs07";
val () = make_definitions_for_file (7, "../../vyper/tests/export/functional/codegen/calling_convention/test_new_call_convention.json");
val () = export_theory_no_docs();
