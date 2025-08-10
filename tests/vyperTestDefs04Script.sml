open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs04";
val () = make_definitions_for_file (4, "../../vyper/tests/export/functional/codegen/calling_convention/test_inlineable_functions.json");
val () = export_theory_no_docs();
