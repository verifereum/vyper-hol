open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs29";
val () = make_definitions_for_file (29, "vyper-test-exports/functional/codegen/types/numbers/test_constants.json");
val () = export_theory_no_docs();
