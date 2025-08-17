open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs34";
val () = make_definitions_for_file (34, "../../vyper/tests/export/functional/codegen/types/numbers/test_modulo.json");
val () = export_theory_no_docs();
