open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs24";
val () = make_definitions_for_file (24, "vyper-test-exports/functional/codegen/integration/test_crowdfund.json");
val () = export_theory_no_docs();
