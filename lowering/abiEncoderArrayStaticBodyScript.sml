(* Execute one actual static-element array body, including its source/address setup. *)
Theory abiEncoderArrayStaticBody
Ancestors
  abiEncoderArrayBodyCode abiEncoderArrayPrepare abiEncoderArrayBounds abiEncoderArrayAddress
  abiEncoderStatic abiEncoderAfterAddress abiEncoderChildFrames abiEncoderDynamic
  abiEncoderChildInputs abiEncoderCorrect abiEncoderAdmissible abiEncoderInput abiDecoderEffect
  abiDecoderContract abiDecoderLoop abiDecoderReentry abiDecoderArrayInitExec
  abiDecoderDynamicLoopSetup fragExec compileEnv valueEncoding contractABI venomState words list
  arithmetic

Theorem abi_encoder_array_static_body_reach:
  abi_encoder_static_leaf ei /\ abi_encode_array_static_body ip src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_encoder_buffer_pre (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size b cap initial /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\ j < LENGTH avs /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (d+32+j*asz) (LENGTH (enc ty (EL j avs))) actual.vs_memory = enc ty (EL j avs) /\
    eval_operand out actual = SOME (n2w j) /\
    abi_decode_footprint_frame [(d+32+j*asz,LENGTH (enc ty (EL j avs)));(b,cap)] initial actual /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_static_body_context >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var /\ first <= prepared.cs_next_id /\
    st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`dyn` |-> `F`] abi_encoder_array_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  `abi_decoder_budget first last b cap ready` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `ready:venom_state`]
      abi_decoder_budget_transport) >>
     impl_tac >- full_simp_tac bool_ss [abi_decoder_address_frame_def] >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_encoder_buffer_pre (AbiDynArray _ _ _ _) _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  disch_then (assume_tac o MATCH_MP abi_encoder_input_typed) >>
  `~is_dynamic ty` by (qpat_assum `F = is_dynamic ty` mp_tac >> simp_tac bool_ss []) >>
  drule_all abi_encoder_array_child_bounds >> strip_tac >>
  qpat_assum `is_static ty ==> _` (fn th =>
    qpat_assum `is_static ty` (assume_tac o MATCH_MP th)) >>
  `j*asz+LENGTH (enc ty (EL j avs)) <= output_size-32 /\ 32 <= output_size` by
    (full_simp_tac bool_ss [] >> decide_tac) >>
  drule abi_encode_array_addresses_shape >> strip_tac >>
  mp_tac (Q.INST [`st` |-> `prepared`, `initial` |-> `ready:venom_state`, `out` |-> `ignored`,
    `src` |-> `SND (FST (coords:(operand # operand) # (operand # operand)))`,
    `dst` |-> `FST (SND (coords:(operand # operand) # (operand # operand)))`,
    `head` |-> `SND (SND (coords:(operand # operand) # (operand # operand)))`,
    `at` |-> `ty:abi_type`, `av` |-> `EL j (avs:abi_value list)`, `offset` |-> `j*asz`,
    `sb` |-> `sb+32+j*msz`, `source_cap` |-> `msz:num`, `d` |-> `d+32`,
    `output_size` |-> `output_size-32`] abi_encoder_static_info_reach) >>
  impl_tac >- full_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready actual` >>
  imp_res_tac abi_encoder_effect_operand >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`,
    `fp` |-> `[(d+32+j*asz,LENGTH (enc ty (EL j avs)));(b,cap)]`] abi_encoder_frame_after_address) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`child_lo` |-> `prepared.cs_next_id`, `child_hi` |-> `end_st.cs_next_id`,
    `child_next` |-> `prepared.cs_next_var`, `child_d` |-> `d+32`, `child_sz` |-> `output_size-32`,
    `lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`, `next` |-> `st.cs_next_var`,
    `sz` |-> `output_size:num`] abi_encoder_after_address) >>
  impl_tac >- (full_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  qpat_assum `asz = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
