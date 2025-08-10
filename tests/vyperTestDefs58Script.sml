open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs58";
val () = make_definitions_for_file (58, "../../vyper/tests/export/functional/codegen/features/test_gas.json");
val () = export_theory_no_docs();
