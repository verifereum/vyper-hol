open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs07";
val () = make_definitions_for_file (7, "../../vyper/tests/export/functional/codegen/calling_convention/test_modifiable_external_contract_calls.json");
val () = export_theory_no_docs();
