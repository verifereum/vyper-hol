open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs38";
val () = make_definitions_for_file (38, "vyper-test-exports/functional/codegen/types/test_bytes.json");
val () = export_theory_no_docs();
