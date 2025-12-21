open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs77";
val () = make_definitions_for_file (77, "vyper-test-exports/functional/codegen/features/decorators/test_private.json");
val () = export_theory_no_docs();
