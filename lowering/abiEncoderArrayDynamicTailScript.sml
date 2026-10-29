(* Execute the real cursor/tail setup, recursive child, and dynamic bookkeeping.
   The selected complete child buffer is supplied by the actual address prefix. *)
Theory abiEncoderArrayDynamicTail
Ancestors
  abiEncoderArraySourceSpine abiEncoderArraySpine abiEncoderMemberSpine
  abiEncoderMemberPhaseRaw abiEncoderMemberSourceAdapter abiEncoderExtendSim
  abiEncoderArrayTailPrepare abiEncoderArrayTail abiEncoderArrayDynamicCode abiEncoderDynamic
  abiEncoderChildCompose abiEncoderChildFrames abiEncoderChildCode abiEncoderChildInputs
  abiEncoderCorrect abiEncoderCounters abiEncoderResultLive abiDecoderEffect
  abiDecoderAllocation abiDecoderProtectedScratch abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderContract abiDecoderLoop fragExec compileEnv valueEncoding venomState finite_map
  pred_set words list arithmetic

Theorem abi_encoder_array_dynamic_tail_reach:
  abi_encoder_correct ei /\
  abi_encode_array_tail data_op dyn_ptr st = (ops,prepared) /\
  compile_abi_encode_to_buf (SND ops) src ei prepared = (child_len,child_end) /\
  abi_encode_child_suffix head dyn_ptr (FST ops) child_len child_end = (child_len,end_st) /\
  fn_has_code st prepared func /\ fn_has_code prepared child_end func /\ fn_has_code child_end end_st func /\
  abi_encoder_buffer_pre ei at av st src data_op sb source_cap d output_size b cap initial /\
  abi_decoder_operand_live st.cs_next_var head /\ eval_operand head initial = SOME (n2w (d+ho)) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ ho+32 <= off /\ off+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= site /\ site < st.cs_next_id /\ lo <= site /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (d+off) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    mem_word_at (d+ho) actual.vs_memory = n2w off /\
    mem_word_at slot actual.vs_memory = n2w (off+LENGTH (enc at av)) /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
    eval_operand child_len actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_decode_footprint_frame [(d+ho,32);(d+off,LENGTH (enc at av));(b,cap)] initial actual /\
    abi_decoder_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encode_array_tail_shape >> strip_tac >> drule abi_encode_child_suffix_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  drule abi_encode_result_live >> strip_tac >> drule_all abi_encode_array_dynamic_body_child_phi >> disch_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var /\ child_end.cs_next_var <= limit_st.cs_next_var /\
    first <= prepared.cs_next_id /\ child_end.cs_next_id <= last /\ site < last /\
    site < prepared.cs_next_id /\ st.cs_next_var <= prepared.cs_next_var /\
    st.cs_next_var <= child_end.cs_next_var` by decide_tac >>
  qpat_assum `abi_encoder_buffer_pre _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_buffer_pre_def]) >>
  `site IN abi_decoder_ids first last` by simp[abi_decoder_ids_def] >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  `b+cap < dimword (:256)` by
    (qpat_assum `abi_decoder_budget _ _ _ _ initial`
       (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decoder_budget_def]) >> simp[]) >>
  `slot < dimword (:256)` by decide_tac >>
  `abi_decoder_operand_live prepared.cs_next_var head /\
    abi_decoder_operand_live child_end.cs_next_var dyn_ptr` by
    (conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `abi_encoder_spine_core_code func (ei,SND ops,src,prepared,child_end,child_len)` by
    fs[abi_encoder_spine_core_code_def] >>
  qabbrev_tac `Pre = \(e,dd,ss,p,en,op:operand) s.
    abi_encoder_correct e /\ abi_encoder_pre e at av p ss dd sb source_cap (d+off) b cap s /\
    abi_decoder_budget first last b cap s /\ first <= p.cs_next_id /\ en.cs_next_id <= last /\
    en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
    abi_decoder_operand_live p.cs_next_var head /\
    abi_decoder_operand_live p.cs_next_var (FST ops) /\
    abi_decoder_operand_live p.cs_next_var dyn_ptr /\
    eval_operand head s = SOME (n2w (d+ho)) /\
    eval_operand (FST ops) s = SOME (n2w off) /\
    eval_operand dyn_ptr s = SOME (n2w slot) /\ first <= site /\ site < last /\ site < p.cs_next_id /\
    FLOOKUP s.vs_allocas site = SOME (slot,32) /\
    ~s.vs_halted /\ s.vs_current_bb = p.cs_current_bb /\ s.vs_inst_idx = LENGTH p.cs_current_insts` >>
  qabbrev_tac `Post = \(e:abi_enc_info,dd:operand,ss:operand,p,en,op) s t.
    mem_bytes_at (d+off) (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand op t = SOME (n2w (LENGTH (enc at av))) /\
    abi_decoder_effect first last p.cs_next_id en.cs_next_id p.cs_next_var
      limit_st (d+off) (LENGTH (enc at av)) b cap s t /\
    eval_operand head t = SOME (n2w (d+ho)) /\
    eval_operand (FST ops) t = SOME (n2w off) /\
    eval_operand dyn_ptr t = SOME (n2w slot) /\ FLOOKUP t.vs_allocas site = SOME (slot,32) /\
    mload slot t = mload slot s /\ fresh_vars_wrt limit_st t /\ abi_decoder_budget first last b cap t /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func s t` >>
  `!c ready. abi_encoder_spine_core_code func c /\ Pre c ready ==>
    ?encoded. Post c ready encoded /\ Post c ready encoded` by
    (rpt gen_tac >> PairCases_on `c` >>
     simp_tac (srw_ss()) [Abbr `Pre`, Abbr `Post`, abi_encoder_spine_core_code_def] >>
     rpt strip_tac >> irule abi_encoder_dynamic_child_core >>
     goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
     goal_assum (drule_at Any) >> asm_rewrite_tac []) >>
  `!ready. abi_encoder_member_phase_raw st prepared initial ready ==>
    Pre (ei,SND ops,src,prepared,child_end,child_len) ready` by
    (rpt strip_tac >> drule_all abi_encoder_array_prepare_raw_transport >> strip_tac >>
     `FLOOKUP ready.vs_allocas site = SOME (slot,32) /\
       eval_operand head ready = SOME (n2w (d+ho))` by
       (qpat_assum `abi_decoder_address_frame _ _ _`
          (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
        conj_tac >- (pure_asm_rewrite_tac [] >> REFL_TAC) >> metis_tac []) >>
     asm_simp_tac (srw_ss()) [Abbr `Pre`] >> decide_tac) >>
  `!ready encoded. Post (ei,SND ops,src,prepared,child_end,child_len) ready encoded ==>
    abi_encoder_spine_cursor_input (head,dyn_ptr,FST ops,child_len,child_end,end_st,limit_st) encoded` by
    (simp_tac (srw_ss()) [Abbr `Post`, abi_encoder_spine_cursor_input_def] >>
     rpt strip_tac >> qexistsl_tac [`d+ho`, `slot`, `off`, `LENGTH (enc at av)`] >>
     asm_rewrite_tac [] >> decide_tac) >>
  drule_all abi_encoder_array_spine_dynamic_run >>
  disch_then (qx_choose_then `ready` (qx_choose_then `encoded` (qx_choose_then `actual` strip_assume_tac))) >>
  qpat_x_assum `Post _ _ _` mp_tac >> simp_tac (srw_ss()) [Abbr `Post`] >> strip_tac >>
  qpat_x_assum `abi_encoder_spine_call _ _ _ _` kall_tac >>
  qpat_x_assum `!c rr. _` kall_tac >>
  qpat_x_assum `!rr. abi_encoder_member_phase_raw _ _ _ _ ==> _` kall_tac >>
  qpat_x_assum `!rr uu. _` kall_tac >>
  qpat_x_assum `Abbrev (Pre = _)` kall_tac >>
  drule_all abi_encoder_array_prepare_raw_transport >> strip_tac >>
  mp_tac (Q.INST [`st` |-> `child_end`, `st'` |-> `end_st`, `out` |-> `child_len`,
    `initial` |-> `encoded:venom_state`, `offset` |-> `FST (ops:operand # operand)`,
    `h` |-> `d+ho`, `len` |-> `LENGTH (enc at av)`, `bytes` |-> `enc at av`,
    `hi` |-> `end_st.cs_next_id`] abi_encoder_source_dynamic_finish_transport) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  `abi_decode_footprint_frame [(d+ho,32);(d+off,LENGTH (enc at av));(b,cap)] initial actual` by
    (mp_tac (Q.INST [`next` |-> `st.cs_next_var`, `h` |-> `d+ho`, `q` |-> `d+off`,
      `len` |-> `LENGTH (enc at av)`] abi_encoder_dynamic_child_frame) >>
     impl_tac >- fs[abi_decoder_effect_def] >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st prepared)` by fs[EVERY_CONJ] >>
  drule_all abi_encoder_member_phase_extend_sim >>
  disch_then (qspec_then `ctx` assume_tac) >> drule abi_encoder_extend_sim_sim >> strip_tac >>
  mp_tac (Q.INST [`child_lo` |-> `prepared.cs_next_id`, `child_hi` |-> `child_end.cs_next_id`,
    `child_next` |-> `prepared.cs_next_var`, `suffix_next` |-> `child_end.cs_next_var`,
    `child_d` |-> `d+off`, `child_sz` |-> `LENGTH (enc at av)`, `sz` |-> `output_size:num`,
    `next` |-> `st.cs_next_var`, `hi` |-> `end_st.cs_next_id`] abi_encoder_child_compose) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  qexists_tac `actual` >> fs[] >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `encoded` >> simp[]
QED

val _ =
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag abi_encoder_array_dynamic_tail_reach) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print "SOURCE_ARRAY_SPINE_AUDIT_OK dynamic_tail_reach\n"
    else raise Fail "source array spine admission dependency"
  end;
