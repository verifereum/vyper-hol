open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs45";
val () = make_definitions_for_file (45, "vyper-test-exports/functional/codegen/types/test_string.json");
val () = export_theory_no_docs();
