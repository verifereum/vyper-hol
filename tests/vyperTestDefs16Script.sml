open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs16";
val () = make_definitions_for_file (16, "vyper-test-exports/functional/codegen/modules/test_exports.json");
val () = export_theory_no_docs();
