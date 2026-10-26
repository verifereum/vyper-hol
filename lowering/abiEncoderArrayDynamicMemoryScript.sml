(* The dynamic body retains the parent source/index and advances its registered tail cursor. *)
Theory abiEncoderArrayDynamicMemory
Ancestors
  abiEncoderArrayMemory abiEncoderArrayCursor abiEncoderArrayDynamicIteration abiEncoderArrayDynamicCode
  abiEncoderArrayPrefix abiEncoderMembersDefs abiEncoderChildInputs abiEncoderCorrect
  abiDecoderEffect abiDecoderContract abiDecoderReentry abiDecoderLoop fragExec compileEnv
  valueEncodingProps valueEncoding contractABI venomState finite_map words list arithmetic

Theorem abi_encoder_array_dynamic_body_memory:
  abi_encoder_correct ei /\ abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func /\
  abi_encoder_array_memory ei asz msz T ty avs owner_st src dst sb source_cap d output_size b cap j initial /\
  abi_encoder_cursor T ip index_site index_slot first lo owner_st j initial /\
  abi_encoder_cursor T dyn_ptr site slot first lo owner_st off initial /\ index_site < site /\
  off = LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) /\
  j < LENGTH avs /\ owner_st.cs_next_var <= st.cs_next_var /\ owner_st.cs_next_id <= st.cs_next_id /\
  abi_decoder_budget first last b cap initial /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_array_memory ei asz msz T ty avs owner_st src dst sb source_cap
      d output_size b cap (SUC j) actual /\
    abi_encoder_cursor T ip index_site index_slot first lo owner_st j actual /\
    abi_encoder_cursor T dyn_ptr site slot first lo owner_st
      (LENGTH avs*abi_member_head_size ty+SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) avs))) actual /\
    eval_operand out actual = SOME (n2w j) /\
    abi_decoder_effect first last site end_st.cs_next_id owner_st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_array_memory _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_array_memory_def]) >>
  qpat_assum `abi_encoder_cursor T ip _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  qpat_assum `abi_encoder_cursor T dyn_ptr _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  drule_all abi_encode_array_dynamic_body_context >> strip_tac >>
  `site < st.cs_next_id /\ index_site < last /\ site < last /\ owner_st.cs_next_id <= last` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `cursor_op` |-> `ip:operand`, `off` |-> `j:num`,
    `site` |-> `index_site:num`, `slot` |-> `index_slot:num`, `s` |-> `initial:venom_state`] abi_encoder_cursor_bounds) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_encoder_buffer_pre (AbiDynArray ei asz msz T) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size b cap initial` by
    (irule abi_encoder_buffer_pre_mono >> qexists_tac `owner_st` >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live st.cs_next_var dyn_ptr` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `owner_st.cs_next_var` >> simp[]) >>
  mp_tac (Q.INST [`p` |-> `n2w index_slot:bytes32`, `lo` |-> `site:num`]
    abi_encoder_array_dynamic_iteration) >>
  impl_tac >- asm_simp_tac (srw_ss()) [w2n_n2w, Excl "enc_def"] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `abi_decoder_effect first last site end_st.cs_next_id owner_st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`d`, `end_st.cs_next_id`, `site`, `st.cs_next_var`, `output_size`] >> simp[]) >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `next` |-> `owner_st.cs_next_var`, `cursor_op` |-> `ip:operand`,
    `site` |-> `index_site:num`, `slot` |-> `index_slot:num`, `active` |-> `T`, `off` |-> `j:num`,
    `sz` |-> `output_size:num`, `owned_lo` |-> `site:num`, `owned_hi` |-> `end_st.cs_next_id`] abi_encoder_cursor_effect_protected) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `next` |-> `owner_st.cs_next_var`, `cursor_op` |-> `dyn_ptr:operand`,
    `active` |-> `T`, `sz` |-> `output_size:num`, `owned_lo` |-> `site:num`, `owned_hi` |-> `end_st.cs_next_id`,
    `next_off` |-> `LENGTH (avs:abi_value list)*abi_member_head_size ty+
      SUM (MAP (abi_member_tail_size ty) (TAKE (SUC j) (avs:abi_value list)))`]
    abi_encoder_cursor_effect_registered) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL, GSYM mem_word_at_eq_mload] >> disch_tac >>
  mp_tac (Q.INST [`st` |-> `owner_st`, `dyn` |-> `T`, `k` |-> `SUC j`, `hi` |-> `end_st.cs_next_id`,
    `lo` |-> `site:num`] abi_encoder_array_memory_advance) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
