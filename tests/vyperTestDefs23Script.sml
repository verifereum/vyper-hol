open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs23";
val () = make_definitions_for_file (23, "../../vyper/tests/export/functional/codegen/integration/test_basics.json");
val () = export_theory_no_docs();
