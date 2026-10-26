(* The actual dynamic-element body advances both the encoded prefix and tail cursor. *)
Theory abiEncoderArrayDynamicIteration
Ancestors
  abiEncoderArrayDynamicBody abiEncoderArrayStep abiEncoderArrayLayout abiEncoderArrayPrefix
  abiEncoderChildInputs abiEncoderInput abiEncoderCorrect abiDecodeRanges
  abiDecoderEffect abiDecoderContract abiDecoderLoop fragExec compileEnv valueEncoding contractABI
  venomState finite_map words list rich_list arithmetic

Theorem abi_encoder_array_tail_sum_suc:
  j < LENGTH avs /\ is_dynamic ty ==>
  SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs)) =
    SUM (MAP (abi_member_tail_size ty) (TAKE j avs))+LENGTH (enc ty (EL j avs))
Proof
  strip_tac >> `TAKE (SUC j) avs = TAKE j avs++[EL j avs]` by simp[TAKE_SUC, TAKE1_DROP] >>
  asm_simp_tac (srw_ss()) [MAP_APPEND, SUM_APPEND, abi_member_tail_size_def, Excl "enc_def"]
QED

Theorem abi_encoder_array_dynamic_iteration:
  abi_encoder_correct ei /\ abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_encoder_buffer_pre (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size b cap initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\ j < LENGTH avs /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\
  off = LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < st.cs_next_id /\ lo <= site /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory /\
    mem_word_at slot actual.vs_memory = n2w (LENGTH avs*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs))) /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\ eval_operand out actual = SOME (n2w j) /\
    abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac abi_encoder_array_dynamic_body_reach >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  qpat_assum `abi_encoder_input (AbiDynArray _ _ _ _) _ _ _ _ _`
    (assume_tac o MATCH_MP abi_encoder_input_typed) >>
  drule_all abi_encoder_array_selected_input >> strip_tac >>
  qpat_assum `asz = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  `is_dynamic ty` by (qpat_assum `T = is_dynamic ty` mp_tac >> simp_tac bool_ss []) >>
  mp_tac abi_encoder_array_dynamic_step >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  drule_all abi_encoder_array_tail_sum_suc >> disch_tac >>
  qexists_tac `actual` >> full_simp_tac bool_ss [ADD_ASSOC]
QED
