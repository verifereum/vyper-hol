Theory vyperTestDefs_functional_codegen_types_test_string[no_sig_docs]
Ancestors jsonToVyper
Libs vyperTestLib
val () = holbuild_extra_deps ["../vyper-test-exports/functional/codegen/types/test_string.json", "../vyper-test-exports/functional/codegen/types/test_string.json.provenance"];
val () = make_definitions_for_file ("functional_codegen_types_test_string", "../vyper-test-exports/functional/codegen/types/test_string.json");

(* ===== Local regression proofs ===== *)
(* Retain completed JSON/CV generation across the bounded build deadline.
   No test selection, trace, expected result or bytecode is changed. *)
Theorem string_trace_nonempty:
  traces_functional_codegen_types_test_string_0 <> []
Proof
  simp[DB.fetch "vyperTestDefs_functional_codegen_types_test_string"
    "traces_functional_codegen_types_test_string_0_def"]
QED
