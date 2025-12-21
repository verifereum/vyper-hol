open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs80";
val () = make_definitions_for_file (80, "vyper-test-exports/functional/codegen/features/decorators/test_raw_return.json");
val () = export_theory_no_docs();
