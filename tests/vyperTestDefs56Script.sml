open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs56";
val () = make_definitions_for_file (56, "../../vyper/tests/export/functional/codegen/features/test_conditionals.json");
val () = export_theory_no_docs();
