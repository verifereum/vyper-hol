open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs04";
val () = make_definitions_for_file (4, "vyper-test-exports/functional/codegen/calling_convention/test_external_contract_calls.json");
val () = export_theory_no_docs();
