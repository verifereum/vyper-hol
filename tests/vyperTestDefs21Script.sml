open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs21";
val () = make_definitions_for_file (21, "vyper-test-exports/functional/codegen/modules/test_nonreentrant.json");
val () = export_theory_no_docs();
