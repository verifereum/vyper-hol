open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs42";
val () = make_definitions_for_file (42, "vyper-test-exports/functional/codegen/types/test_identifier_naming.json");
val () = export_theory_no_docs();
