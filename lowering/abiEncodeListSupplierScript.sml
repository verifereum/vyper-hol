Theory abiEncodeListSupplier
Ancestors
  abiEncodeZeroSupplier abiEncodeArgsSim abiEncodeTupleCongruence
  abiEncoderSourceAggregate abiEncoderSourcePrimitive abiTupleEncodeZeroInput
  abiTupleEncodeLayout exprSimDefs exprSimProps loweringPosts compileEnv valueEncoding vyperABI vyperValue
  contractABI abiDecodeRanges vyperTyping words list

Theorem abi_encode_word_head_size[local]:
  is_word_type ty /\ evaluate_type env ty = SOME tv ==>
  abi_member_head_size (vyper_to_abi_type env ty) = 32
Proof
  Cases_on `ty` >> simp[is_word_type_def]
  >- (rename1 `BaseT bt` >> Cases_on `bt` >>
      simp[is_word_type_def, evaluate_type_def, vyper_base_to_abi_type_def,
           abi_member_head_size_def, is_dynamic_def, static_length_def] >>
      rename1 `BytesT bound` >> Cases_on `bound` >>
      simp[is_word_type_def, evaluate_type_def, vyper_base_to_abi_type_def,
           abi_member_head_size_def, is_dynamic_def, static_length_def]) >>
  rw[evaluate_type_def, vyper_to_abi_type_def, AllCaseEqs(),
     abi_member_head_size_def, is_dynamic_def, static_length_def]
QED

Theorem abi_encode_fresh_zero_input_supplier[local]:
  expr_val_rel cx ty v op s /\ expr_val_at ce cx ty sa st es v op s /\
  stmt_state_rel ctx func ce cx es s /\ s.vs_alloca_next <= lo /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\
  abi_enc_plan (get_tenv cx) ty (type_to_abi_enc_info sf ce ty) /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_bytes ce ty < dimword (:256) /\
  abi_decoder_operand_live next op /\
  abi_embedded_static_size ce.ce_struct_fields ty =
    abi_member_head_size (vyper_to_abi_type (get_tenv cx) ty) /\
  is_abi_dynamic ce.ce_struct_fields ty =
    is_dynamic (vyper_to_abi_type (get_tenv cx) ty) ==>
  ?ct rv. enc ct rv = enc (vyper_to_abi_type (get_tenv cx) ty) av /\
    abi_tuple_encode_zero_input sf ce ty ct rv op next lo hi s /\
    abi_tuple_encode_layout ce [(op,ty)] [ct] /\
    is_dynamic ct = is_dynamic (vyper_to_abi_type (get_tenv cx) ty) /\
    abi_member_head_size ct = abi_member_head_size (vyper_to_abi_type (get_tenv cx) ty)
Proof
  strip_tac >>
  `?ct rv. enc ct rv = enc (vyper_to_abi_type (get_tenv cx) ty) av /\
    abi_tuple_encode_zero_input sf ce ty ct rv op next lo hi s /\
    abi_tuple_encode_layout ce [(op,ty)] [ct]` by
    (Cases_on `is_word_type ty`
     >- (drule_all abi_encode_word_head_size >> strip_tac >>
         drule_all abi_encoder_word_source_shape >> strip_tac >>
         irule abi_encode_word_zero_input_supplier >> metis_tac[]) >>
     drule_all abi_encode_fresh_nonword_zero_input_supplier >> metis_tac[]) >>
  qexistsl_tac [`ct`, `rv`] >>
  gvs[abi_tuple_encode_layout_def]
QED

Theorem abi_encode_args_zero_input_representatives:
  !args vs ops cavs.
  abi_args_post ctx func ce cx es sa st s0 es' args ops vs s /\
  EVERY (abi_decoder_operand_live next) ops /\ s.vs_alloca_next <= lo /\
  LIST_REL (\(e,v) av. ?tv.
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\ value_has_type tv v /\
    vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME av /\
    abi_enc_plan (get_tenv cx) (lowered_value_type ce e) (type_to_abi_enc_info sf ce (lowered_value_type ce e)) /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
    type_memory_bytes ce (lowered_value_type ce e) < dimword (:256) /\
    abi_embedded_static_size ce.ce_struct_fields (lowered_value_type ce e) =
      abi_member_head_size (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) /\
    is_abi_dynamic ce.ce_struct_fields (lowered_value_type ce e) =
      is_dynamic (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)))
    (ZIP (args,vs)) cavs ==>
  ?ats avs.
    abi_tuple_encode_zero_inputs sf ce (ZIP (ops,MAP (lowered_value_type ce) args)) ats avs next lo hi s /\
    abi_tuple_encode_layout ce (ZIP (ops,MAP (lowered_value_type ce) args)) ats /\
    LIST_REL (\(at,av) (bt,bv).
      enc at av = enc bt bv /\ is_dynamic at = is_dynamic bt /\
      abi_member_head_size at = abi_member_head_size bt)
      (ZIP (ats,avs))
      (ZIP (MAP (vyper_to_abi_type (get_tenv cx) o lowered_value_type ce) args,cavs))
Proof
  Induct
  >- (simp[abi_args_post_nil] >> rpt strip_tac >> gvs[] >>
      simp[abi_tuple_encode_zero_inputs_def, abi_tuple_encode_layout_def]) >>
  rpt gen_tac >> strip_tac >>
  `LENGTH (h::args) = LENGTH vs /\ LENGTH ops = LENGTH (h::args)` by
    metis_tac[abi_args_post_lengths] >>
  Cases_on `vs` >> Cases_on `ops` >> Cases_on `cavs` >> gvs[] >>
  gvs[abi_args_post_cons] >>
  `stmt_state_rel ctx func ce cx es' s` by gvs[abi_args_post_def] >>
  `type_memory_bytes ce (lowered_value_type ce h) < dimword (:256)` by simp[] >>
  drule_all abi_encode_fresh_zero_input_supplier >>
  disch_then (qspec_then `hi` strip_assume_tac) >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`ct::ats`, `rv::avs`] >>
  simp[abi_tuple_encode_zero_inputs_def, abi_tuple_encode_layout_def] >>
  gvs[abi_tuple_encode_layout_def] >> metis_tac[]
QED

Theorem abi_encode_args_zero_input_supplier:
  abi_args_post ctx func ce cx es sa st s0 es' args ops vs s /\
  EVERY (abi_decoder_operand_live next) ops /\ s.vs_alloca_next <= lo /\
  LIST_REL (\(e,v) av. ?tv.
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\ value_has_type tv v /\
    vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME av /\
    abi_enc_plan (get_tenv cx) (lowered_value_type ce e) (type_to_abi_enc_info sf ce (lowered_value_type ce e)) /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
    type_memory_bytes ce (lowered_value_type ce e) < dimword (:256) /\
    abi_embedded_static_size ce.ce_struct_fields (lowered_value_type ce e) =
      abi_member_head_size (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)) /\
    is_abi_dynamic ce.ce_struct_fields (lowered_value_type ce e) =
      is_dynamic (vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e)))
    (ZIP (args,vs)) cavs ==>
  ?ats avs.
    abi_tuple_encode_zero_inputs sf ce (ZIP (ops,MAP (lowered_value_type ce) args)) ats avs next lo hi s /\
    abi_tuple_encode_layout ce (ZIP (ops,MAP (lowered_value_type ce) args)) ats /\
    enc (Tuple ats) (ListV avs) =
      enc (Tuple (MAP (vyper_to_abi_type (get_tenv cx) o lowered_value_type ce) args)) (ListV cavs)
Proof
  strip_tac >>
  `LENGTH args = LENGTH vs` by metis_tac[abi_args_post_lengths] >>
  `LENGTH args = LENGTH cavs` by
    (drule LIST_REL_LENGTH >> simp[]) >>
  drule_all abi_encode_args_zero_input_representatives >>
  disch_then (qspec_then `hi` strip_assume_tac) >>
  drule abi_tuple_encode_zero_inputs_lengths >> strip_tac >>
  qexistsl_tac [`ats`, `avs`] >> asm_simp_tac bool_ss [] >>
  irule abi_encode_tuple_congruence >> simp[]
QED
