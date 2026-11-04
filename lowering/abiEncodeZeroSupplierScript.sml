Theory abiEncodeZeroSupplier
Ancestors
  abiEncodeOwnership abiEncodeInputSupplier abiTupleEncodeZeroInput
  abiEncoderSourceAggregate abiEncoderSourceFootprint abiTupleEncodeLayout
  exprSim valueEncodingProps valueEncodingTyping valueEncoding vyperTyping words

Theorem abi_encode_nonword_zero_input_supplier:
  ~is_word_type ty /\ expr_val_rel cx ty v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\
  abi_enc_plan (get_tenv cx) ty (type_to_abi_enc_info sf ce ty) /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_bytes ce ty < dimword (:256) /\
  abi_decoder_operand_live next op /\
  (!w. eval_operand op s = SOME w ==>
    val_footprint tv v = 0 \/ w2n w + val_footprint tv v <= lo \/ hi <= w2n w) /\
  abi_embedded_static_size ce.ce_struct_fields ty =
    abi_member_head_size (vyper_to_abi_type (get_tenv cx) ty) /\
  is_abi_dynamic ce.ce_struct_fields ty =
    is_dynamic (vyper_to_abi_type (get_tenv cx) ty) ==>
  ?ct rv. source_rep (get_tenv cx) ty (type_to_abi_enc_info sf ce ty) ct /\
    enc ct rv = enc (vyper_to_abi_type (get_tenv cx) ty) av /\
    abi_tuple_encode_zero_input sf ce ty ct rv op next lo hi s /\
    abi_tuple_encode_layout ce [(op,ty)] [ct]
Proof
  strip_tac >>
  qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
  simp[expr_val_rel_def] >> strip_tac >>
  `val_in_memory tv v (w2n w) s.vs_memory` by metis_tac[] >>
  drule_all abi_encoder_source_footprint_rep >> strip_tac >>
  `val_wf tv v` by metis_tac[cj 1 value_has_type_val_wf] >>
  drule val_footprint_le >> strip_tac >>
  drule_all source_rep_compiler_layout >> strip_tac >>
  qexistsl_tac [`ct`, `rv`] >> simp[] >> conj_tac
  >- (simp[abi_tuple_encode_zero_input_def] >>
      qexistsl_tac [`w2n w`, `val_footprint tv v`] >> simp[w2n_lt] >>
      metis_tac[]) >>
  simp[abi_tuple_encode_layout_def] >> metis_tac[]
QED

Theorem abi_encode_fresh_nonword_zero_input_supplier:
  ~is_word_type ty /\ expr_val_rel cx ty v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\
  abi_enc_plan (get_tenv cx) ty (type_to_abi_enc_info sf ce ty) /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_bytes ce ty < dimword (:256) /\
  abi_decoder_operand_live next op /\
  stmt_state_rel ctx func ce cx es s /\
  expr_val_at ce cx ty sa st es v op s /\ s.vs_alloca_next <= lo /\
  abi_embedded_static_size ce.ce_struct_fields ty =
    abi_member_head_size (vyper_to_abi_type (get_tenv cx) ty) /\
  is_abi_dynamic ce.ce_struct_fields ty =
    is_dynamic (vyper_to_abi_type (get_tenv cx) ty) ==>
  ?ct rv. source_rep (get_tenv cx) ty (type_to_abi_enc_info sf ce ty) ct /\
    enc ct rv = enc (vyper_to_abi_type (get_tenv cx) ty) av /\
    abi_tuple_encode_zero_input sf ce ty ct rv op next lo hi s /\
    abi_tuple_encode_layout ce [(op,ty)] [ct]
Proof
  strip_tac >>
  irule abi_encode_nonword_zero_input_supplier >>
  goal_assum (drule_at Any) >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`tv`, `v`] >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >> drule_all abi_encode_fresh_footprint_separation >> simp[]
QED
