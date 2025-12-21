open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs33";
val () = make_definitions_for_file (33, "vyper-test-exports/functional/codegen/types/numbers/test_isqrt.json");
val () = export_theory_no_docs();
