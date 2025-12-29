open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs58";
val () = make_definitions_for_file (58, "vyper-test-exports/functional/codegen/features/test_flag_pure_functions.json");
val () = export_theory_no_docs();
