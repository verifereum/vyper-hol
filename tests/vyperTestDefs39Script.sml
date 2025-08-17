open HolKernel vyperTestLib;
val () = new_theory "vyperTestDefs39";
val () = make_definitions_for_file (39, "../../vyper/tests/export/functional/codegen/types/test_bytes_literal.json");
val () = export_theory_no_docs();
