open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs78";
val () = make_definitions_for_file (78, "../../vyper/tests/export/functional/codegen/features/decorators/test_public.json");
val () = export_theory_no_docs();
