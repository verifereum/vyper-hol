open HolKernel jsonToVyperTheory vyperTestLib;
val () = new_theory "vyperTestDefs81";
val () = make_definitions_for_file (81, "vyper-test-exports/functional/codegen/features/decorators/test_view.json");
val () = export_theory_no_docs();
