(* Execute one actual dynamic-element array body from its parent source input. *)
Theory abiEncoderArrayDynamicBody
Ancestors
  abiEncoderArrayDynamicCode abiEncoderArrayDynamicTail abiEncoderArrayPrepare
  abiEncoderArrayBounds abiEncoderArrayAddress abiEncoderAfterAddress abiEncoderChildFrames
  abiEncoderDynamic abiEncoderChildInputs abiEncoderInput abiEncoderCorrect
  abiDecoderArrayInitExec abiDecoderDynamicLoopSetup abiDecoderEffect abiDecoderContract
  abiDecoderLoop abiDecoderReentry fragExec compileEnv valueEncoding contractABI venomState
  finite_map words list arithmetic

Theorem abi_encoder_array_dynamic_body_reach:
  abi_encoder_correct ei /\ abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_encoder_buffer_pre (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size b cap initial /\
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
  ?actual. mem_bytes_at (d+32+off) (LENGTH (enc ty (EL j avs))) actual.vs_memory = enc ty (EL j avs) /\
    mem_word_at (d+32+j*asz) actual.vs_memory = n2w off /\
    mem_word_at slot actual.vs_memory = n2w (off+LENGTH (enc ty (EL j avs))) /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\ eval_operand out actual = SOME (n2w j) /\
    abi_decode_footprint_frame [(d+32+j*asz,32);(d+32+off,LENGTH (enc ty (EL j avs)));(b,cap)] initial actual /\
    abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_dynamic_body_context >> strip_tac >>
  `addressed.cs_next_var <= limit_st.cs_next_var /\ site < addressed.cs_next_id /\
    st.cs_next_var <= addressed.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`dyn` |-> `T`, `prepared` |-> `addressed`] abi_encoder_array_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  qpat_assum `asz = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  `abi_decoder_budget first last b cap ready` by
    (mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `ready:venom_state`]
      abi_decoder_budget_transport) >>
     impl_tac >- full_simp_tac bool_ss [abi_decoder_address_frame_def] >> asm_simp_tac bool_ss []) >>
  qpat_assum `abi_encoder_buffer_pre (AbiDynArray _ _ _ _) _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  disch_then (assume_tac o MATCH_MP abi_encoder_input_typed) >>
  `is_dynamic ty` by (qpat_assum `T = is_dynamic ty` mp_tac >> simp_tac bool_ss []) >>
  drule_all abi_encoder_array_child_bounds >> strip_tac >>
  qpat_assum `is_dynamic ty ==> _` (fn th => qpat_assum `is_dynamic ty` (MAP_EVERY assume_tac o CONJUNCTS o MATCH_MP th)) >>
  `j*abi_member_head_size ty+32 <= off /\ off+LENGTH (enc ty (EL j avs)) <= output_size-32` by
    (full_simp_tac bool_ss [] >> decide_tac) >>
  drule abi_encode_array_addresses_shape >> strip_tac >>
  `abi_decoder_operand_live addressed.cs_next_var dyn_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand dyn_ptr ready = SOME (n2w slot) /\ mload slot ready = n2w off /\
    FLOOKUP ready.vs_allocas site = SOME (slot,32)` by
    full_simp_tac (srw_ss()) [abi_decoder_address_frame_def, mload_def, Excl "enc_def"] >>
  mp_tac (Q.INST [`st` |-> `addressed`, `initial` |-> `ready:venom_state`,
    `src` |-> `SND (FST (coords:(operand # operand) # (operand # operand)))`,
    `data_op` |-> `FST (SND (coords:(operand # operand) # (operand # operand)))`,
    `head` |-> `SND (SND (coords:(operand # operand) # (operand # operand)))`,
    `at` |-> `ty:abi_type`, `av` |-> `EL j (avs:abi_value list)`, `ho` |-> `j*abi_member_head_size ty`,
    `sb` |-> `sb+32+j*msz`, `source_cap` |-> `msz:num`, `d` |-> `d+32`,
    `output_size` |-> `output_size-32`] abi_encoder_array_dynamic_tail_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready actual` >> imp_res_tac abi_encoder_effect_operand >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`,
    `fp` |-> `[(d+32+j*abi_member_head_size ty,32);(d+32+off,LENGTH (enc ty (EL j avs)));(b,cap)]`]
    abi_encoder_frame_after_address) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`child_lo` |-> `lo:num`, `child_hi` |-> `end_st.cs_next_id`,
    `child_next` |-> `addressed.cs_next_var`, `child_d` |-> `d+32`, `child_sz` |-> `output_size-32`,
    `hi` |-> `end_st.cs_next_id`, `next` |-> `st.cs_next_var`, `sz` |-> `output_size:num`]
    abi_encoder_after_address) >>
  impl_tac >- (full_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
