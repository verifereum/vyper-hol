(* The actual static-element body advances complete source/output observations.
   TOP-LEVEL: abi_scratch_array_static_body_memory retains the registered index
   and complete source contract at the loop's stable compiler entry. *)
Theory abiScratchArrayStaticMemory
Ancestors
  abiScratchArrayStaticBody abiScratchStatic abiScratchInput abiScratchCursor
  abiScratchEncoderContract abiScratchEffect abiEncoderArrayBodyCode abiEncoderArrayCursor
  abiEncoderMembersDefs abiEncoderArrayPrefix abiDecoderAllocation abiDecoderFootprint
  abiDecoderReentry abiDecoderLoop abiDecoderContract compileEnv valueEncoding contractABI
  venomState words list arithmetic

Theorem abi_scratch_array_static_body_memory:
  abi_encoder_static_leaf ei /\ abi_encode_array_static_body ip src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    owner_st src dst sb source_cap d output_size first last b cap initial /\
  abi_encoder_array_prefix ty avs j d initial.vs_memory /\
  abi_encoder_cursor T ip site slot first lo owner_st j initial /\ j < LENGTH avs /\
  owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= st.cs_next_id /\
  abi_decoder_budget first last b cap initial /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
      owner_st src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs (SUC j) d actual.vs_memory /\
    abi_encoder_cursor T ip site slot first lo owner_st j actual /\ eval_operand out actual = SOME (n2w j) /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id owner_st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_cursor T ip _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  drule_all abi_encode_array_static_body_context >> strip_tac >>
  `owner_st.cs_next_id <= last /\ first <= st.cs_next_id /\ site < last /\ site < st.cs_next_id` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `cursor_op` |-> `ip:operand`, `off` |-> `j:num`,
    `s` |-> `initial:venom_state`] abi_encoder_cursor_bounds) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_scratch_input (AbiDynArray ei asz msz F) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial` by
    (irule abi_scratch_input_mono >> qexists_tac `owner_st` >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`p` |-> `n2w slot:bytes32`] abi_scratch_array_static_body_reach) >>
  impl_tac >- asm_simp_tac (srw_ss()) [w2n_n2w, Excl "enc_def"] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  drule_all abi_scratch_array_static_bounds >> strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ owner_st _ _ _ _ _ _ _ _ _ _ initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  qpat_assum `asz = _` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  mp_tac (Q.INST [`fp` |-> `abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial`]
    abi_scratch_array_static_step) >> impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id owner_st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_scratch_effect_widen >>
     qexistsl_tac [`d`, `end_st.cs_next_id`, `st.cs_next_id`, `st.cs_next_var`, `output_size`] >> simp[]) >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `cursor_op` |-> `ip:operand`, `active` |-> `T`, `off` |-> `j:num`,
    `owned_lo` |-> `st.cs_next_id`, `owned_hi` |-> `end_st.cs_next_id`, `next` |-> `owner_st.cs_next_var`,
    `sz` |-> `output_size:num`] abi_scratch_cursor_protected) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  mp_tac (Q.INST [`ei` |-> `AbiDynArray ei (abi_member_head_size ty) msz F`, `at` |-> `Array NONE ty`,
    `av` |-> `ListV avs`, `st` |-> `owner_st`, `lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
    `next` |-> `owner_st.cs_next_var`, `sz` |-> `output_size:num`] abi_scratch_input_effect) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
