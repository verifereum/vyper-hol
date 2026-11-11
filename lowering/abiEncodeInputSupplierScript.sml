(* Endpoint-facing metadata for encoding-equivalent source representatives. *)
Theory abiEncodeInputSupplier
Ancestors
  abiEncoderSourceAggregate abiCallerTupleLayout abiDecodeRanges exprLowering compileEnv
  abiEncoderSourceFootprint abiTupleEncodeOpenInput abiTupleEncodeLayout
  exprSimDefs exprSimProps loweringPosts valueEncodingProps valueEncodingTyping valueEncoding vyperTyping words

Theorem source_rep_static_memory:
  source_rep env ty ei ct /\ evaluate_type env ty = SOME tv /\
  ~is_dynamic ct ==>
  static_length ct = type_memory_size tv
Proof
  strip_tac >> drule_all source_rep_metadata >> strip_tac >>
  `~is_dynamic (vyper_to_abi_type env ty)` by metis_tac[] >>
  drule_all abi_caller_static_memory >>
  gvs[abi_member_head_size_def]
QED

Theorem source_rep_compiler_layout:
  source_rep env ty ei ct /\ evaluate_type env ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\
  abi_embedded_static_size ce.ce_struct_fields ty =
    abi_member_head_size (vyper_to_abi_type env ty) /\
  is_abi_dynamic ce.ce_struct_fields ty =
    is_dynamic (vyper_to_abi_type env ty) ==>
  abi_embedded_static_size ce.ce_struct_fields ty = abi_member_head_size ct /\
  is_abi_dynamic ce.ce_struct_fields ty = is_dynamic ct /\
  (~is_dynamic ct ==> type_memory_bytes ce ty = static_length ct)
Proof
  strip_tac >> drule_all source_rep_metadata >> strip_tac >>
  simp[] >> metis_tac[source_rep_static_memory]
QED

Theorem abi_encode_nonword_input_supplier:
  ~is_word_type ty /\ expr_val_rel cx ty v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) ty v = SOME av /\
  abi_enc_plan (get_tenv cx) ty (type_to_abi_enc_info sf ce ty) /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_bytes ce ty < dimword (:256) /\
  abi_decoder_operand_live next op /\
  (!w. eval_operand op s = SOME w ==>
    w2n w + val_footprint tv v <= lo \/ hi <= w2n w) /\
  abi_embedded_static_size ce.ce_struct_fields ty =
    abi_member_head_size (vyper_to_abi_type (get_tenv cx) ty) /\
  is_abi_dynamic ce.ce_struct_fields ty =
    is_dynamic (vyper_to_abi_type (get_tenv cx) ty) ==>
  ?ct rv. source_rep (get_tenv cx) ty (type_to_abi_enc_info sf ce ty) ct /\
    enc ct rv = enc (vyper_to_abi_type (get_tenv cx) ty) av /\
    abi_tuple_encode_open_input sf ce ty ct rv op next lo hi s /\
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
  >- (simp[abi_tuple_encode_open_input_def] >>
      qexistsl_tac [`w2n w`, `val_footprint tv v`] >> simp[w2n_lt] >>
      metis_tac[]) >>
  simp[abi_tuple_encode_layout_def] >> metis_tac[]
QED
