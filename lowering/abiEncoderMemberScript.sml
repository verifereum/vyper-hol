Theory abiEncoderMember
Ancestors
  abiEncoderMemberSourceAdapter
  abiEncoderBufferFrame abiEncoderAddressReach abiEncoderChildInputs abiEncoderInput
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderContract abiDecoderLoop fragExec
  emitHelperProps compileEnv valueEncoding venomState words list arithmetic abiEncoderStatic
  abiEncoderDynamic abiEncoderTuple abiEncoderCorrect abiDecoderEffect abiDecoderAllocation
  valueEncodingProps abiCanonicalWindows finite_map

(* ===== Prepare ===== *)

(* The emitted member-source ADD establishes the selected child's complete input. *)

Theorem abi_encoder_member_prepare:
  emit_op ADD [src;Lit (n2w (abi_encoder_member_span (TAKE i infos)))] st = (elem_src,prepared) /\
  fn_has_code st prepared func /\
  abi_encoder_buffer_pre (AbiComplex infos) at (ListV avs)
    st src dst sb source_cap d output_size b cap initial /\
  abi_encoder_tuple_type at ats /\ i < LENGTH infos /\ EL i infos = (ei,abi_sz,mem_sz,dyn) /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready. abi_encoder_buffer_pre ei (EL i ats) (EL i avs) prepared elem_src dst
      (sb+abi_encoder_member_span (TAKE i infos)) mem_sz d output_size b cap ready /\
    abi_sz = abi_member_head_size (EL i ats) /\ dyn = is_dynamic (EL i ats) /\
    abi_decoder_operand_live prepared.cs_next_var elem_src /\ fresh_vars_wrt limit_st ready /\
    abi_decoder_address_frame st.cs_next_var initial ready /\
    ready.vs_current_bb = prepared.cs_current_bb /\ ready.vs_inst_idx = LENGTH prepared.cs_current_insts /\
    ~ready.vs_halted /\ abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  drule emitted_insts_emit_op >> strip_tac >> drule abi_decoder_operand_live_emit >> strip_tac >>
  mp_tac (Q.INST [`opc` |-> `ADD`, `lhs` |-> `src`,
    `rhs` |-> `Lit (n2w (abi_encoder_member_span (TAKE i infos)))`, `out` |-> `elem_src`,
    `st'` |-> `prepared`, `a` |-> `n2w sb:bytes32`,
    `b` |-> `n2w (abi_encoder_member_span (TAKE i infos)):bytes32`] abi_encoder_binary_reach) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial ready` >>
  `eval_operand elem_src ready = SOME (n2w (sb+abi_encoder_member_span (TAKE i infos)))`
    by fs[word_add_n2w] >>
  `st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`child_st` |-> `prepared`, `child_src` |-> `elem_src`,
    `actual` |-> `ready:venom_state`] abi_encoder_member_buffer_pre) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `ready` >> asm_simp_tac bool_ss []
QED

(* ===== Step ===== *)

(* Actual static/dynamic child compilation advances the tuple-prefix invariant. *)

Theorem abi_encoder_static_member_step:
  abi_encoder_correct ei /\ compile_abi_encode_child dst src ei F heads dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_buffer_pre ei ty av st src dst sb source_cap d output_size b cap initial /\
  LENGTH pre = LENGTH pvs /\ ~is_dynamic ty /\
  heads = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  tails = LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  heads+LENGTH (enc ty av) <= hl /\ hl+tails <= output_size /\
  abi_encoder_tuple_prefix hl pre pvs d initial.vs_memory /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. abi_encoder_tuple_prefix hl (pre++[ty]) (pvs++[av]) d t.vs_memory /\
    eval_operand out t = SOME (n2w (LENGTH (enc ty av))) /\
    abi_decode_footprint_frame [(d+heads,LENGTH (enc ty av));(b,cap)] initial t /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `heads+LENGTH (enc ty av) <= output_size` by decide_tac >>
  mp_tac (Q.INST [`at` |-> `ty:abi_type`, `offset` |-> `heads:num`] abi_encoder_static_child_spine_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  mp_tac abi_encoder_tuple_static_step >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_dynamic_member_step:
  abi_encoder_correct ei /\ compile_abi_encode_child dst src ei T heads dyn_ptr st = (out,end_st) /\
  fn_has_code st end_st func /\
  (st.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_buffer_pre ei ty av st src dst sb source_cap d output_size b cap initial /\
  LENGTH pre = LENGTH pvs /\ is_dynamic ty /\
  heads = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  tails = LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  heads+32 <= hl /\ off = hl+tails /\ off+LENGTH (enc ty av) <= output_size /\
  abi_encoder_tuple_prefix hl pre pvs d initial.vs_memory /\
  eval_operand dyn_ptr initial = SOME (n2w slot) /\ mload slot initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < st.cs_next_id /\ lo <= site /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. abi_encoder_tuple_prefix hl (pre++[ty]) (pvs++[av]) d t.vs_memory /\
    mload slot t = n2w (off+LENGTH (enc ty av)) /\ FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    eval_operand out t = SOME (n2w (LENGTH (enc ty av))) /\
    abi_decode_footprint_frame [(d+heads,32);(d+off,LENGTH (enc ty av));(b,cap)] initial t /\
    abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> `heads+32 <= off` by decide_tac >>
  mp_tac (Q.INST [`at` |-> `ty:abi_type`, `head_offset` |-> `heads:num`] abi_encoder_dynamic_child_spine_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  mp_tac abi_encoder_tuple_dynamic_step >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [GSYM mem_word_at_eq_mload]
QED
