(* Rich observations from the generator's supplied static child endpoint. *)
Theory abiEncoderSharedMembersOutput
Ancestors
  abiEncoderSharedMemberContract abiEncoderMemberSpineCompat abiEncoderSharedContract
  abiEncoderScratchTransport abiEncoderSharedSuffix
  abiEncoderChildContext abiEncoderMemberSpine abiEncoderAddressReach
  abiScratchEffect abiScratchEncoderContract abiDecoderDynamicLoopSetup
  abiScratchFootprint abiDecoderContract abiDecoderLoop
  abiScratchMemberAdapter abiEncoderChildSuffixReach abiScratchChild abiDecoderReentry abiDecoderProtectedScratch abiDecoderAllocation
  abiEncoderMemberPhaseRaw abiEncoderMemberPhaseExec
  abiEncoderRegisteredEffect abiEncoderExtendSim valueEncoding contractABI
  compileEnv venomState words list arithmetic

Theorem abi_encoder_shared_member_static_output:
  compile_abi_encode_child dst src ei F offset dp st = (out,en) /\
  fn_has_code st en func /\
  (st.cs_blocks = en.cs_blocks \/
    !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap)
    (d,output_size) (first,last,b,cap) initial /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_spine_child_output
    (abi_encoder_spine_shared_post (ctx,func) (at,av,sb,source_cap,d+offset)
      (first,last,b,cap,limit_st))
    (ei,F,dst,src,offset,dp,st,en,out) initial actual ==>
  abi_encoder_shared_endpoint (ctx,func) (st,en,out,limit_st)
    (first,last,b,cap) (at,av,d+offset) initial actual
Proof
  simp_tac bool_ss [abi_encoder_spine_child_output_def, abi_encoder_spine_shared_post_def] >>
  disch_then (MAP_EVERY strip_assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_static_child_structural_context >> strip_tac >>
  gvs[] >> drule abi_encoder_emit_address_shape >> strip_tac >>
  `p.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `eval_operand dst initial = SOME (n2w d)` by fs[abi_encoder_shared_input_def] >>
  drule_all abi_encoder_spine_static_shared_transport >> simp[]
QED

Theorem abi_encoder_shared_member_dynamic_output:
  compile_abi_encode_child dst src ei T ho dp st = (out,en) /\
  abi_encode_child_prefix dst ho dp st = (ops,prepared) /\ fn_has_code st en func /\
  (st.cs_blocks = en.cs_blocks \/
    !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_shared_input (ei,at,av) (st,src,dst) (sb,source_cap)
    (d,output_size) (first,last,b,cap) initial /\
  eval_operand dp initial = SOME (n2w slot) /\ mload slot initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var dp /\
  ho+32 <= off /\ off+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= lo /\ lo <= site /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ en.cs_next_id <= last /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_spine_child_output
    (abi_encoder_shared_member_dynamic_post (ctx,func) (at,av,sb,source_cap,d+off)
      (first,last,b,cap,limit_st) (FST ops,FST (SND ops),dp,d+ho,off,slot,site))
    (ei,T,dst,src,ho,dp,st,en,out) initial actual ==>
  mem_bytes_at (d+off) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
  mem_word_at (d+ho) actual.vs_memory = n2w off /\
  mem_word_at slot actual.vs_memory = n2w (off+LENGTH (enc at av)) /\
  FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
  eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
  abi_scratch_effect first last lo en.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual /\
  abi_encoder_registered_effect (abi_decoder_ids lo en.cs_next_id) [(d,output_size)] initial actual /\
  (alloca_inv initial ==> alloca_inv actual) /\ abi_encoder_extend_sim ctx func initial actual /\
  actual.vs_current_bb = en.cs_current_bb /\ actual.vs_inst_idx = LENGTH en.cs_current_insts /\
  ~actual.vs_halted /\
  abi_decode_footprint_frame
    ([(d+ho,32);(d+off,LENGTH (enc at av))] ++
      abi_decoder_child_scratch (abi_decoder_ids lo en.cs_next_id) b cap initial) initial actual
Proof
  simp_tac bool_ss [abi_encoder_spine_child_output_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `?ops p len ce r u. _` mp_tac >>
  disch_then (qx_choose_then `child_ops` mp_tac) >>
  disch_then (qx_choose_then `p` mp_tac) >>
  disch_then (qx_choose_then `child_len` mp_tac) >>
  disch_then (qx_choose_then `ce` mp_tac) >>
  disch_then (qx_choose_then `r` mp_tac) >>
  disch_then (qx_choose_then `u` mp_tac) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_dynamic_child_context >> strip_tac >> gvs[] >>
  drule abi_encoder_shared_member_dynamic_saved >> strip_tac >>
  qpat_assum `abi_encoder_shared_member_dynamic_post _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_member_dynamic_post_def]) >>
  fs[abi_encoder_spine_shared_post_def, abi_encoder_spine_core_code_def] >> gvs[] >>
  `p.cs_next_var <= limit_st.cs_next_var /\ ce.cs_next_var <= limit_st.cs_next_var /\
    first <= p.cs_next_id /\ ce.cs_next_id <= last /\
    site < p.cs_next_id /\ st.cs_next_var <= p.cs_next_var /\
    st.cs_next_var <= ce.cs_next_var /\ lo <= p.cs_next_id /\
    site IN abi_decoder_ids lo en.cs_next_id /\ site IN abi_decoder_ids first last` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `slot < dimword (:256)` by
    (qpat_assum `abi_decoder_budget _ _ _ _ initial`
       (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >>
     simp_tac bool_ss [] >> decide_tac) >>
  `eval_operand dst initial = SOME (n2w d) /\
    abi_decoder_operand_live st.cs_next_var dst /\ d+output_size < dimword (:256)` by
    fs[abi_encoder_shared_input_def] >>
  `d+ho < dimword (:256) /\ d <= d+ho /\ d+ho+32 <= d+output_size /\
    d <= d+off /\ d+off+LENGTH (enc at av) <= d+output_size` by decide_tac >>
  `abi_decoder_operand_live ce.cs_next_var dp` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  drule_all abi_encoder_member_prefix_transport >> strip_tac >>
  `abi_decoder_address_frame st.cs_next_var initial r` by asm_rewrite_tac [] >>
  `abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial)` by
    fs[abi_encoder_shared_input_def] >>
  `abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap r)` by
    (drule_all abi_encoder_address_scratch_disjoint >> simp[]) >>
  qpat_x_assum `abi_encoder_shared_input _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `abi_encoder_shared_member_dynamic_post _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `abi_encoder_shared_member_dynamic_pre _ _ _ _ _` kall_tac >>
  qpat_x_assum `compile_abi_encode_child _ _ _ _ _ _ _ = _` kall_tac >>
  `ce.cs_next_id <= en.cs_next_id` by decide_tac >>
  drule_all (SRULE [] (Q.INST [`hi` |-> `en.cs_next_id`, `next` |-> `st.cs_next_var`]
    abi_encoder_spine_dynamic_shared_effects)) >> strip_tac >>
  drule_all abi_encoder_spine_dynamic_shared_sim >>
  disch_then assume_tac >>
  drule abi_encoder_shared_endpoint_scratch >> disch_tac >>
  `eval_operand child_len u = SOME (n2w (LENGTH (enc at av)))` by
    fs[abi_encoder_shared_endpoint_def] >>
  drule_all abi_encoder_spine_cursor_post >> disch_tac >>
  drule_all (SRULE [] (Q.INST [`hi` |-> `en.cs_next_id`, `next` |-> `st.cs_next_var`]
    abi_scratch_child_effect)) >> strip_tac >>
  `d+ho+32 <= d+off` by decide_tac >>
  drule_all abi_encoder_shared_suffix_observations >> strip_tac >>
  asm_rewrite_tac []
QED
