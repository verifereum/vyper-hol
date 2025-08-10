open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs28";
val () = make_definitions_for_file (28, "../../vyper/tests/export/functional/codegen/types/numbers/test_constants.json");
val () = export_theory_no_docs();
