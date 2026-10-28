(* Execute setup, the recursive child and bookkeeping in the containing CFG.
   TOP-LEVEL: abi_scratch_array_dynamic_tail_reach composes all three actual
   stages under the child induction hypothesis and returns one precise effect. *)
Theory abiScratchArrayDynamicTail
Ancestors
  abiScratchArraySpine abiEncoderArraySpine abiScratchMemberAdapter
  abiEncoderMemberSpine abiEncoderMemberPhaseRaw abiEncoderExtendSim
  abiScratchArrayTail abiScratchEncoderRun abiScratchChild abiScratchEncoderContract
  abiScratchFootprint abiScratchEffect abiEncoderArrayTail abiEncoderChildCode
  abiEncoderChildSuffixReach abiDecoderDynamicLoopSetup abiDecoderAllocation abiDecoderFootprint
  abiDecoderFrame abiDecoderReentry abiDecoderContract abiDecoderLoop compileEnv valueEncoding
  contractABI venomState finite_map pred_set words list arithmetic

Theorem abi_scratch_array_dynamic_tail_reach:
  abi_scratch_encoder ei /\
  abi_encode_array_tail data_op dyn_ptr st = (ops,prepared) /\
  compile_abi_encode_to_buf (SND ops) src ei prepared = (child_len,child_end) /\
  abi_encode_child_suffix head dyn_ptr (FST ops) child_len child_end = (child_len,end_st) /\
  fn_has_code st prepared func /\ fn_has_code prepared child_end func /\ fn_has_code child_end end_st func /\
  abi_scratch_input ei at av st src data_op sb source_cap d output_size first last b cap initial /\
  abi_decoder_operand_live st.cs_next_var head /\ eval_operand head initial = SOME (n2w (d+ho)) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ ho+32 <= off /\ off+LENGTH (enc at av) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= lo /\ lo <= site /\ site < st.cs_next_id /\
  FLOOKUP initial.vs_allocas site = SOME (slot,32) /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (d+off) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    mem_word_at (d+ho) actual.vs_memory = n2w off /\
    mem_word_at slot actual.vs_memory = n2w (off+LENGTH (enc at av)) /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\
    eval_operand child_len actual = SOME (n2w (LENGTH (enc at av))) /\
    abi_encoder_input ei at av sb source_cap actual.vs_memory /\
    abi_decode_footprint_frame
      ([(d+ho,32);(d+off,LENGTH (enc at av))] ++
        abi_decoder_child_scratch (abi_decoder_ids lo end_st.cs_next_id) b cap initial) initial actual /\
    abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_array_tail_code >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand data_op initial = SOME (n2w d) /\
    abi_decoder_operand_live st.cs_next_var data_op /\
    d+output_size < dimword (:256)` by fs[abi_scratch_input_def] >>
  `abi_encoder_spine_core_code func (ei,SND ops,src,prepared,child_end,child_len)` by
    fs[abi_encoder_spine_core_code_def] >>
  qabbrev_tac `Pre = \(e,dd,ss,p,en,op:operand) s.
    abi_scratch_encoder e /\ abi_scratch_input e at av p ss dd sb source_cap (d+off)
      (LENGTH (enc at av)) first last b cap s /\
    abi_decoder_budget first last b cap s /\ first <= p.cs_next_id /\ en.cs_next_id <= last /\
    en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
    abi_decoder_operand_live p.cs_next_var head /\
    abi_decoder_operand_live p.cs_next_var (FST ops) /\
    abi_decoder_operand_live p.cs_next_var dyn_ptr /\
    eval_operand head s = SOME (n2w (d+ho)) /\
    eval_operand (FST ops) s = SOME (n2w off) /\
    eval_operand dyn_ptr s = SOME (n2w slot) /\ first <= site /\ site < p.cs_next_id /\
    FLOOKUP s.vs_allocas site = SOME (slot,32) /\
    ~s.vs_halted /\ s.vs_current_bb = p.cs_current_bb /\ s.vs_inst_idx = LENGTH p.cs_current_insts` >>
  qabbrev_tac `Post = \(e:abi_enc_info,dd:operand,ss:operand,p,en,op) s t.
    mem_bytes_at (d+off) (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand op t = SOME (n2w (LENGTH (enc at av))) /\
    abi_encoder_input e at av sb source_cap t.vs_memory /\
    abi_scratch_effect first last p.cs_next_id en.cs_next_id p.cs_next_var
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
     rpt strip_tac >> irule abi_scratch_dynamic_child_core >>
     goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
     goal_assum (drule_at Any) >> asm_rewrite_tac []) >>
  `!ready. abi_encoder_member_phase_raw st prepared initial ready ==>
    Pre (ei,SND ops,src,prepared,child_end,child_len) ready` by
    (rpt strip_tac >> drule_all abi_scratch_array_prepare_raw_transport >> strip_tac >>
     fs[Abbr `Pre`, abi_decoder_address_frame_def] >> decide_tac) >>
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
  drule_all abi_scratch_array_prepare_raw_transport >> strip_tac >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap ready encoded` by fs[abi_scratch_effect_def] >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial encoded` by
    (drule_all abi_scratch_evolution_trans >> simp[]) >>
  `abi_footprint_disjoint d output_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap encoded)` by
    (mp_tac (Q.INST [`ids` |-> `abi_decoder_ids first last`, `b` |-> `b:num`, `cap` |-> `cap:num`,
       `p` |-> `d:num`, `n` |-> `output_size:num`, `s` |-> `initial:venom_state`,
       `t` |-> `encoded:venom_state`] abi_scratch_disjoint_advance) >>
     impl_tac >- fs[abi_scratch_input_def] >> simp[]) >>
  `d <= d+ho /\ d+ho+32 <= d+off` by decide_tac >>
  drule_all abi_scratch_dynamic_finish_raw_transport >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `lo <= prepared.cs_next_id /\ child_end.cs_next_id <= end_st.cs_next_id /\
    st.cs_next_var <= prepared.cs_next_var /\
    site IN abi_decoder_ids lo end_st.cs_next_id /\
    d <= d+off /\ (d+off)+LENGTH (enc at av) <= d+output_size /\ d+ho+32 <= d+output_size` by
    (simp[abi_decoder_ids_def] >> decide_tac) >>
  drule_all abi_scratch_child_effect >> strip_tac >>
  `abi_encoder_input ei at av sb source_cap actual.vs_memory` by
    (irule (Q.INST [`s` |-> `initial:venom_state`, `st` |-> `st:compile_state`,
       `dst` |-> `data_op:operand`, `lo` |-> `lo:num`, `hi` |-> `end_st.cs_next_id`]
       abi_scratch_effect_source) >>
     goal_assum (drule_at Any) >> asm_rewrite_tac [] >>
     goal_assum (drule_at Any) >> asm_rewrite_tac []) >>
  drule abi_encode_array_tail_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st prepared)` by fs[EVERY_CONJ] >>
  drule_all abi_encoder_member_phase_extend_sim >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_encoder_extend_sim_sim >> strip_tac >>
  qexists_tac `actual` >> fs[] >>
  irule abi_decode_sim_trans >> qexists_tac `ready` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `encoded` >> simp[]
QED

val _ =
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag abi_scratch_array_dynamic_tail_reach) in
    if List.all (fn s => s = "DISK_THM") oracles andalso null axioms then
      print "SCRATCH_ARRAY_SPINE_AUDIT_OK dynamic_tail_reach\n"
    else raise Fail "scratch array spine admission dependency"
  end;
