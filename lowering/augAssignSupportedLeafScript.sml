(* Structural closure at a base descriptor, independent of runtime typing. *)
Theory augAssignSupportedLeaf
Ancestors
  supportedTypes

Theorem supported_nested_base_leaf:
  supported_nested_type leaf fuel tops (BaseT b) ==> leaf (BaseT b)
Proof
  simp[Once supported_nested_type_def]
QED
