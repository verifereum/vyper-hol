open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs03";
val () = make_definitions_for_file (3, "../../vyper/tests/export/functional/codegen/calling_convention/test_default_function.json");
val () = export_theory_no_docs();
