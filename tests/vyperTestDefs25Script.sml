open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs25";
val () = make_definitions_for_file (25, "../../vyper/tests/export/functional/codegen/integration/test_escrow.json");
val () = export_theory_no_docs();
