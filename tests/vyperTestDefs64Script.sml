open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs64";
val () = make_definitions_for_file (64, "../../vyper/tests/export/functional/codegen/features/test_mana.json");
val () = export_theory_no_docs();
