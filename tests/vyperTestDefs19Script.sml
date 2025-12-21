open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs19";
val () = make_definitions_for_file (19, "vyper-test-exports/functional/codegen/modules/test_module_constants.json");
val () = export_theory_no_docs();
