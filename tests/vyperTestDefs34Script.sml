open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs34";
val () = make_definitions_for_file (34, "vyper-test-exports/functional/codegen/types/numbers/test_modulo.json");
val () = export_theory_no_docs();
