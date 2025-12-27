open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs37";
val () = make_definitions_for_file (37, "vyper-test-exports/functional/codegen/types/test_array_indexing.json");
val () = export_theory_no_docs();
