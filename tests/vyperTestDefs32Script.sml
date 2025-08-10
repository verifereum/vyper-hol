open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs32";
val () = make_definitions_for_file (32, "../../vyper/tests/export/functional/codegen/types/numbers/test_isqrt.json");
val () = export_theory_no_docs();
