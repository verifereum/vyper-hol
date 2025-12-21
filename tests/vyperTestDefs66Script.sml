open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs66";
val () = make_definitions_for_file (66, "vyper-test-exports/functional/codegen/features/test_memory_alloc.json");
val () = export_theory_no_docs();
