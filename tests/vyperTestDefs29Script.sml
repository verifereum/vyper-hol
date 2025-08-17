open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs29";
val () = make_definitions_for_file (29, "../../vyper/tests/export/functional/codegen/types/numbers/test_constants.json");
val () = export_theory_no_docs();
