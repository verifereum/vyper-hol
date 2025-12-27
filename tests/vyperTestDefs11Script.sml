open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs11";
val () = make_definitions_for_file (11, "vyper-test-exports/functional/codegen/environment_variables/test_blobbasefee.json");
val () = export_theory_no_docs();
