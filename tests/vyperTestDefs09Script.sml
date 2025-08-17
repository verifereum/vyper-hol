open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs09";
val () = make_definitions_for_file (9, "../../vyper/tests/export/functional/codegen/calling_convention/test_return.json");
val () = export_theory_no_docs();
