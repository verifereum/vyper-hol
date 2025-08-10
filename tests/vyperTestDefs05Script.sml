open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs05";
val () = make_definitions_for_file (5, "../../vyper/tests/export/functional/codegen/calling_convention/test_internal_call.json");
val () = export_theory_no_docs();
