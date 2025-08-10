open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs75";
val () = make_definitions_for_file (75, "../../vyper/tests/export/functional/codegen/features/decorators/test_payable.json");
val () = export_theory_no_docs();
