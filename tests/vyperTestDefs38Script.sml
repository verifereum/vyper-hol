open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs38";
val () = make_definitions_for_file (38, "../../vyper/tests/export/functional/codegen/types/test_bytes.json");
val () = export_theory_no_docs();
