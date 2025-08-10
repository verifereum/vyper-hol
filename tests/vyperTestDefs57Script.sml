open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs57";
val () = make_definitions_for_file (57, "../../vyper/tests/export/functional/codegen/features/test_gas.json");
val () = export_theory_no_docs();
