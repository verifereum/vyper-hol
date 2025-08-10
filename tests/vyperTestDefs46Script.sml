open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs46";
val () = make_definitions_for_file (46, "../../vyper/tests/export/functional/codegen/types/test_struct.json");
val () = export_theory_no_docs();
