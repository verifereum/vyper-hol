open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs45";
val () = make_definitions_for_file (45, "../../vyper/tests/export/functional/codegen/types/test_string.json");
val () = export_theory_no_docs();
