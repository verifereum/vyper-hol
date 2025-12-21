open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs68";
val () = make_definitions_for_file (68, "vyper-test-exports/functional/codegen/features/test_packing.json");
val () = export_theory_no_docs();
