open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs57";
val () = make_definitions_for_file (57, "vyper-test-exports/functional/codegen/features/test_constructor.json");
val () = export_theory_no_docs();
