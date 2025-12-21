open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs18";
val () = make_definitions_for_file (18, "vyper-test-exports/functional/codegen/modules/test_interface_imports.json");
val () = export_theory_no_docs();
