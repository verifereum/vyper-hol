open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs50";
val () = make_definitions_for_file (50, "../../vyper/tests/export/functional/codegen/features/test_assignment.json");
val () = export_theory_no_docs();
