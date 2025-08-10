open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs40";
val () = make_definitions_for_file (40, "../../vyper/tests/export/functional/codegen/types/test_flag.json");
val () = export_theory_no_docs();
