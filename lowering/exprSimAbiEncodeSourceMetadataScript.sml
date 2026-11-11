(* Compiler metadata projected from the real expression boundary. *)
Theory exprSimAbiEncodeSourceMetadata
Ancestors
  abiEncodeEndpointMetadata exprSimHypsDefs compileEnv

Theorem abi_encode_body_evaluated_metadata:
  expr_body_pre ce cx env e es /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_bytes ce ty MOD 32 = 0 /\
  is_abi_dynamic ce.ce_struct_fields ty = vyper_is_dynamic (get_tenv cx) ty /\
  abi_size_bound ce.ce_struct_fields ty = vyper_abi_size_bound (get_tenv cx) ty
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es` by gvs[expr_body_pre_def] >>
  drule_all abi_encode_endpoint_memory_layout >> strip_tac >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    fs[expr_sim_inv_def] >>
  drule_all abi_encode_evaluated_metadata >> simp[]
QED
