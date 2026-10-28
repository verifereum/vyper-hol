Theory vyperTestDefs_functional_codegen_types_test_dynamic_array[no_sig_docs]
Ancestors vyperTestDefs_functional_codegen_types_test_dynamic_array_part_0
  vyperTestDefs_functional_codegen_types_test_dynamic_array_part_64
  vyperTestDefs_functional_codegen_types_test_dynamic_array_part_128

(* A proof boundary lets holbuild retain the expensive JSON/CV generation
   across infrastructure deadlines, without changing test selection. *)
Theorem dynamic_array_trace_nonempty:
  traces_functional_codegen_types_test_dynamic_array_0 <> []
Proof
  simp[DB.fetch "vyperTestDefs_functional_codegen_types_test_dynamic_array_part_0"
    "traces_functional_codegen_types_test_dynamic_array_0_def"]
QED
