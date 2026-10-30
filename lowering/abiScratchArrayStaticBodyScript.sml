(* Execute the real static-element array body with complete physical resources.
   TOP-LEVEL: abi_scratch_array_static_body_reach composes actual address setup
   and static child execution. Helper: the selected static element fits its head. *)
Theory abiScratchArrayStaticBody
Ancestors
  abiScratchStatic abiScratchArrayPrepare abiScratchArrayCount abiScratchAfterAddress
  abiScratchFrameCompose abiScratchEncoderContract abiScratchEffect abiEncoderArrayBodyCode
  abiEncoderArrayBounds abiEncoderArrayAddress abiEncoderAdmissible abiDecoderAllocation
  abiDecoderFootprint abiDecoderFrame abiDecoderReentry abiDecoderDynamicLoopSetup
  abiDecoderLoop abiDecoderContract compileEnv valueEncoding contractABI venomState pred_set
  words list arithmetic

Theorem abi_scratch_array_static_bounds:
  abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial /\ j < LENGTH avs ==>
  has_type (Array NONE ty) (ListV avs) /\ ~is_dynamic ty /\ asz = abi_member_head_size ty /\
  LENGTH (enc (Array NONE ty) (ListV avs)) <= output_size /\ 32 <= output_size /\
  j*asz+LENGTH (enc ty (EL j avs)) <= output_size-32
Proof
  strip_tac >> drule abi_scratch_array_input_facts >> strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule_all abi_encoder_array_child_bounds >> strip_tac >>
  gvs[Excl "enc_def"] >> decide_tac
QED

Theorem abi_scratch_array_static_body_reach:
  abi_encoder_static_leaf ei /\ abi_encode_array_static_body ip src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\ j < LENGTH avs /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (d+32+j*asz) (LENGTH (enc ty (EL j avs))) actual.vs_memory = enc ty (EL j avs) /\
    eval_operand out actual = SOME (n2w j) /\
    abi_decode_footprint_frame
      ((d+32+j*asz,LENGTH (enc ty (EL j avs)))::
        abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) initial actual /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_static_body_context >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var /\ first <= prepared.cs_next_id /\
   st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  drule_all abi_scratch_array_static_bounds >> strip_tac >>
  mp_tac (Q.INST [`active` |-> `F`] abi_scratch_array_prepare) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  drule abi_encode_array_addresses_shape >> strip_tac >>
  mp_tac (Q.INST [`st` |-> `prepared`, `initial` |-> `ready:venom_state`, `out` |-> `ignored`,
    `src` |-> `SND (FST (coords:(operand # operand) # (operand # operand)))`,
    `dst` |-> `FST (SND (coords:(operand # operand) # (operand # operand)))`,
    `head` |-> `SND (SND (coords:(operand # operand) # (operand # operand)))`,
    `at` |-> `ty:abi_type`, `av` |-> `EL j (avs:abi_value list)`, `offset` |-> `j*asz`,
    `sb` |-> `sb+32+j*msz`, `source_cap` |-> `msz:num`, `d` |-> `d+32`,
    `output_size` |-> `output_size-32`] abi_scratch_static_info_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready actual` >>
  `eval_operand (FST (FST coords)) actual = SOME (n2w j)` by
    (mp_tac (Q.INST [`op` |-> `FST (FST (coords:(operand # operand) # (operand # operand)))`,
      `w` |-> `n2w j:bytes32`, `s` |-> `ready:venom_state`, `t` |-> `actual:venom_state`,
      `next` |-> `prepared.cs_next_var`, `d` |-> `d+32`, `sz` |-> `output_size-32`,
      `lo` |-> `prepared.cs_next_id`, `hi` |-> `end_st.cs_next_id`] abi_scratch_effect_operand) >>
     asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`,
    `child_ids` |-> `abi_decoder_ids prepared.cs_next_id end_st.cs_next_id`,
    `fp` |-> `[(d+32+j*asz,LENGTH (enc ty (EL j avs)))]`,
    `s` |-> `ready:venom_state`, `t` |-> `actual:venom_state`] abi_scratch_frame_subset_append) >>
  impl_tac >- (gvs[APPEND, Excl "enc_def"] >> simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >> disch_tac >>
  mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`, `next` |-> `st.cs_next_var`,
    `fp` |-> `[(d+32+j*asz,LENGTH (enc ty (EL j avs)))]`] abi_scratch_frame_after_address) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  mp_tac (Q.INST [`child_lo` |-> `prepared.cs_next_id`, `child_hi` |-> `end_st.cs_next_id`,
    `child_next` |-> `prepared.cs_next_var`, `child_d` |-> `d+32`, `child_sz` |-> `output_size-32`,
    `lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`, `next` |-> `st.cs_next_var`,
    `sz` |-> `output_size:num`] abi_scratch_effect_after_address) >>
  impl_tac >- (asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >> disch_tac >>
  qexists_tac `actual` >> gvs[] >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> simp[]
QED
