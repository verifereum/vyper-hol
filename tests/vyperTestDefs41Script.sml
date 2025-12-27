open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs41";
val () = make_definitions_for_file (41, "vyper-test-exports/functional/codegen/types/test_flag.json");
val () = export_theory_no_docs();
