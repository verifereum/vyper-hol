open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs46";
val () = make_definitions_for_file (46, "vyper-test-exports/functional/codegen/types/test_string_literal.json");
val () = export_theory_no_docs();
