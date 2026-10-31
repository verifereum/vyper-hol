Theory abiEncoderArrayDynamicMemory
Ancestors
  abiEncoderArrayCode abiEncoderArrayTail abiEncoderArrayBodyCode abiEncoderChildCode
  abiEncoderChildContext abiEncoderCounters abiEncoderAppend abiEncoderResultLive abiEncoderPhi
  abiDecoderContract fragExec compileEnv emitHelperProps emitHelper venomInst venomExecSemantics
  list rich_list arithmetic abiEncoderArraySourceSpine abiEncoderMemberSpine
  abiEncoderMemberPhaseRaw abiEncoderMemberSourceAdapter abiEncoderExtendSim
  abiEncoderArrayTailPrepare abiEncoderDynamic abiEncoderChildCompose abiEncoderChildFrames
  abiEncoderChildInputs abiEncoderCorrect abiDecoderEffect abiDecoderAllocation
  abiDecoderProtectedScratch abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderLoop
  valueEncoding venomState finite_map pred_set words abiEncoderAfterAddress abiEncoderInput
  abiDecoderArrayInitExec contractABI abiEncoderArrayStep abiEncoderArrayPrefix abiDecodeRanges
  abiEncoderArrayMemory abiEncoderArrayHeaderMemory abiEncoderMembersDefs valueEncodingProps
Libs
  monadsyntax

(* Factor the actual dynamic-element body without changing instruction order.
   TOP-LEVEL: exact phases, trace and containing-code/counter context. *)
Theorem abi_encode_array_dynamic_body_phases:
  abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz =
    do coords <- abi_encode_array_addresses ip src dst asz msz;
       ops <- abi_encode_array_tail (FST (SND coords)) dyn_ptr;
       child_len <- compile_abi_encode_to_buf (SND ops) (SND (FST coords)) ei;
       abi_encode_child_suffix (SND (SND coords)) dyn_ptr (FST ops) child_len;
       return (FST (FST coords))
    od
Proof
  simp_tac bool_ss [FUN_EQ_THM, abi_encode_array_dynamic_body_def, abi_encode_array_tail_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_encode_array_dynamic_body_trace:
  abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz st = (out,end_st) ==>
  ?coords addressed ops prepared child_len child_end.
    abi_encode_array_addresses ip src dst asz msz st = (coords,addressed) /\
    abi_encode_array_tail (FST (SND coords)) dyn_ptr addressed = (ops,prepared) /\
    compile_abi_encode_to_buf (SND ops) (SND (FST coords)) ei prepared = (child_len,child_end) /\
    abi_encode_child_suffix (SND (SND coords)) dyn_ptr (FST ops) child_len child_end = (child_len,end_st) /\
    out = FST (FST coords)
Proof
  simp_tac bool_ss [abi_encode_array_dynamic_body_phases, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac abi_encode_child_suffix_shape >> gvs[] >>
  rename1 `abi_encode_array_addresses _ _ _ _ _ st = (coords,addressed)` >>
  rename1 `abi_encode_array_tail _ _ addressed = (ops,prepared)` >>
  rename1 `compile_abi_encode_to_buf _ _ ei prepared = (child_len,child_end)` >>
  qexistsl_tac [`coords`, `addressed`, `ops`, `prepared`, `child_len`, `child_end`] >>
  asm_simp_tac bool_ss []
QED

Theorem abi_encode_array_dynamic_body_context:
  abi_encode_array_dynamic_body ip dyn_ptr src dst ei asz msz st = (out,end_st) /\
  fn_has_code st end_st func ==>
  ?coords addressed ops prepared child_len child_end.
    abi_encode_array_addresses ip src dst asz msz st = (coords,addressed) /\
    abi_encode_array_tail (FST (SND coords)) dyn_ptr addressed = (ops,prepared) /\
    compile_abi_encode_to_buf (SND ops) (SND (FST coords)) ei prepared = (child_len,child_end) /\
    abi_encode_child_suffix (SND (SND coords)) dyn_ptr (FST ops) child_len child_end = (child_len,end_st) /\
    out = FST (FST coords) /\
    fn_has_code st addressed func /\ fn_has_code addressed prepared func /\
    fn_has_code prepared child_end func /\ fn_has_code child_end end_st func /\
    addressed.cs_next_id = st.cs_next_id+7 /\ addressed.cs_next_var = st.cs_next_var+7 /\
    prepared.cs_next_id = addressed.cs_next_id+2 /\ prepared.cs_next_var = addressed.cs_next_var+2 /\
    prepared.cs_next_id <= child_end.cs_next_id /\ prepared.cs_next_var <= child_end.cs_next_var /\
    child_end.cs_next_id+3 = end_st.cs_next_id /\ child_end.cs_next_var+1 = end_st.cs_next_var /\
    addressed.cs_blocks = st.cs_blocks /\ prepared.cs_blocks = addressed.cs_blocks /\
    end_st.cs_blocks = child_end.cs_blocks /\ end_st.cs_current_bb = child_end.cs_current_bb /\
    abi_decoder_operand_live child_end.cs_next_var child_len
Proof
  strip_tac >> drule abi_encode_array_dynamic_body_trace >> strip_tac >>
  drule abi_encode_array_addresses_shape >> strip_tac >>
  drule abi_encode_array_tail_shape >> strip_tac >> drule abi_encode_child_suffix_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >> drule cs_extends_abi_encode >> strip_tac >>
  drule abi_encode_result_live >> strip_tac >>
  `cs_extends st addressed /\ cs_extends addressed prepared /\ cs_extends child_end end_st` by
    (rpt conj_tac >> irule abi_encoder_straight_extends >> asm_simp_tac bool_ss []) >>
  `cs_extends prepared end_st` by
    (irule cs_extends_trans >> qexists_tac `child_end` >> asm_simp_tac bool_ss []) >>
  `cs_extends addressed end_st` by
    (irule cs_extends_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`st`, `addressed`, `end_st`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.SPECL [`addressed`, `prepared`, `end_st`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  mp_tac (Q.SPECL [`prepared`, `child_end`, `end_st`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexistsl_tac [`coords`, `addressed`, `ops`, `prepared`, `child_len`, `child_end`] >>
  asm_simp_tac bool_ss []
QED

Theorem abi_encode_child_suffix_zero_phi:
  abi_encode_child_suffix head dyn_ptr offset child_len st = (out,st') /\
  phi_prefix_length st.cs_current_insts = 0 /\ fn_has_code st st' func ==>
  !bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  simp_tac bool_ss [abi_encode_child_suffix_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  Cases_on `st.cs_current_insts` >> gvs[phi_prefix_length_def, mk_inst_def] >>
  rename1 `inst.inst_opcode = PHI` >> Cases_on `inst.inst_opcode = PHI` >> gvs[]
QED

Theorem abi_encode_array_dynamic_body_child_phi:
  compile_abi_encode_to_buf child_dst child_src ei prepared = (child_len,child_end) /\
  abi_encode_child_suffix head dyn_ptr offset child_len child_end = (child_len,end_st) /\
  fn_has_code child_end end_st func ==>
  prepared.cs_blocks = child_end.cs_blocks \/
  !bb. lookup_block child_end.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_core_exit_phi >> disch_tac >>
  Cases_on `prepared.cs_blocks = child_end.cs_blocks` >- asm_simp_tac bool_ss [] >>
  `phi_prefix_length child_end.cs_current_insts = 0` by full_simp_tac bool_ss [] >>
  mp_tac (Q.INST [`st` |-> `child_end`, `st'` |-> `end_st`, `out` |-> `child_len`]
    abi_encode_child_suffix_zero_phi) >>
  impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []
QED

(* Execute the real cursor/tail setup, recursive child, and dynamic bookkeeping.
   The selected complete child buffer is supplied by the actual address prefix. *)
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
     rpt strip_tac >> irule abi_encoder_source_dynamic_core_run >>
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

(* Execute one actual dynamic-element array body from its parent source input. *)
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

(* The actual dynamic-element body advances both the encoded prefix and tail cursor. *)
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

(* The dynamic body retains the parent source/index and advances its registered tail cursor. *)
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
