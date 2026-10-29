Theory vyperTestDefs_functional_codegen_types_test_dynamic_array[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/types/test_dynamic_array.json", "../vyper-test-exports/functional/codegen/types/test_dynamic_array.json.provenance"];
val () = make_definitions_for_file_range ("functional_codegen_types_test_dynamic_array", "../vyper-test-exports/functional/codegen/types/test_dynamic_array.json", 0, 48);

(* A proof boundary lets holbuild retain the expensive JSON/CV generation
   across infrastructure deadlines, without changing test selection. *)
Theorem dynamic_array_trace_nonempty:
  traces_functional_codegen_types_test_dynamic_array_0 <> []
Proof
  simp[DB.fetch "vyperTestDefs_functional_codegen_types_test_dynamic_array"
    "traces_functional_codegen_types_test_dynamic_array_0_def"]
QED
