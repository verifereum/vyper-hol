(* Namespace-independent ABI metadata at successful source evaluation. *)
Theory exprSimAbiEncodePlanMetadata
Ancestors
  exprSimAbiEncodeSourceMetadata abiEncodeEndpointMetadata
  retAbiPlanProps abiDecodeRanges exprSimHypsDefs compileEnv

Theorem abi_encode_translated_dynamic:
  evaluate_type E ty = SOME tv /\ sfields_tenv_consistent sf E ==>
  is_abi_dynamic sf ty = is_dynamic (vyper_to_abi_type E ty)
Proof
  metis_tac[abi_encode_evaluated_metadata, cj 1 vyper_to_abi_type_dynamic]
QED

Theorem abi_encode_translated_head:
  evaluate_type E ty = SOME tv /\ sfields_tenv_consistent sf E ==>
  abi_embedded_static_size sf ty = abi_member_head_size (vyper_to_abi_type E ty)
Proof
  strip_tac >>
  drule_all abi_encode_evaluated_metadata >> strip_tac >>
  drule (cj 1 vyper_to_abi_type_dynamic) >> strip_tac >>
  simp[abi_embedded_static_size_def, abi_member_head_size_def] >>
  Cases_on `vyper_is_dynamic E ty` >> simp[] >>
  drule_all (cj 1 vyper_to_abi_static_length) >> simp[]
QED

Theorem abi_encode_element_metadata:
  E SUBMAP E0 /\
  sfields_tenv_consistent ce.ce_struct_fields E0 /\
  (!t v. evaluate_type E0 t = SOME v ==>
    type_memory_bytes ce t = type_memory_size v) /\
  evaluate_type E ty = SOME tv ==>
  is_abi_dynamic ce.ce_struct_fields ty = is_dynamic (vyper_to_abi_type E ty) /\
  abi_embedded_static_size ce.ce_struct_fields ty =
    (if is_dynamic (vyper_to_abi_type E ty) then 32
     else static_length (vyper_to_abi_type E ty)) /\
  abi_size_bound ce.ce_struct_fields ty = vyper_abi_size_bound E0 ty /\
  type_memory_bytes ce ty = type_memory_size tv
Proof
  strip_tac >>
  drule (cj 1 vyper_to_abi_type_submap) >> disch_then drule >> strip_tac >>
  drule_all abi_encode_translated_dynamic >> strip_tac >>
  drule_all abi_encode_translated_head >> strip_tac >>
  drule_all abi_encode_evaluated_metadata >> strip_tac >>
  fs[abi_member_head_size_def]
QED

Theorem abi_encode_body_translated_metadata:
  expr_body_pre ce cx env e es /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  is_abi_dynamic ce.ce_struct_fields ty =
    is_dynamic (vyper_to_abi_type (get_tenv cx) ty) /\
  abi_embedded_static_size ce.ce_struct_fields ty =
    abi_member_head_size (vyper_to_abi_type (get_tenv cx) ty)
Proof
  strip_tac >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    fs[expr_body_pre_def, expr_sim_inv_def] >>
  metis_tac[abi_encode_translated_dynamic, abi_encode_translated_head]
QED
