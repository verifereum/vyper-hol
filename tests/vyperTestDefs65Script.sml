open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs65";
val () = make_definitions_for_file (65, "../../vyper/tests/export/functional/codegen/features/test_memory_dealloc.json");
val () = export_theory_no_docs();
