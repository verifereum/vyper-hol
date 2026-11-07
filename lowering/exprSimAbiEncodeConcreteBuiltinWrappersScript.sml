Theory exprSimAbiEncodeConcreteBuiltinWrappers
Ancestors
  exprSimAbiEncodeOpenSetup exprSimAbiEncodeConcreteCompose
  abiBuiltinEncodeAllocate context abiBuiltinEncodeMethod abiBuiltinAllocation
  abiEncodeWindowBuiltin abiBuiltinEncodeCorrect abiBuiltinEncodeCode
  abiEncoderSequence abiEncoderWindowContract abiEncoderRegisteredEffect
  abiDecoderContract abiDecoderFrame abiDecoderLoop compileEnv venomState venomInst
  words list arithmetic abiEncoderWindowSequence abiEncoderWindowLookup
  exprLoweringProps venomExecSemantics venomInstProps
  ctorAbiActualObservations ctorAbiActualWorld abiDecoderReentry
  emitHelper emitHelperProps abiBuiltinEncodeSetup rich_list abiDecoderVarSequence instIdxIndep

Theorem abi_encode_finish_opcodes[local]:
  abi_builtin_encode_finish buf encoded_len mid_size st = ((),final) ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st final)
Proof
  Cases_on `mid_size > 0` >>
  simp[abi_builtin_encode_finish_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
    emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem abi_encode_window_finish_concrete:
  abi_builtin_encode_finish buf encoded_len mid_size st = ((),final) /\
  fn_has_code st final func /\
  eval_operand buf encoded = SOME (n2w p) /\
  eval_operand encoded_len encoded = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var buf /\
  p < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st encoded /\ ~encoded.vs_halted /\
  encoded.vs_current_bb = st.cs_current_bb /\
  encoded.vs_inst_idx = LENGTH st.cs_current_insts /\
  mem_bytes_at (p+32) (mid_size+len) encoded.vs_memory = bytes /\
  window_strong_result ctx func body_st body_end out at av d initial encoded ==>
  ?raw.
    run_inst_seq (emitted_insts st final) encoded = OK raw /\
    inst_extends st final /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st final) /\
    let actual = raw with vs_inst_idx := LENGTH final.cs_current_insts in
    eval_operand buf actual = SOME (n2w p) /\
    mload p actual = n2w (len+mid_size) /\
    mem_bytes_at (p+32) (mid_size+len) actual.vs_memory = bytes /\
    fresh_vars_wrt limit_st actual /\
    abi_decode_frame p 32 encoded actual /\
    abi_encoder_registered_effect {} [(p,32)] encoded actual /\
    actual.vs_allocas = encoded.vs_allocas /\
    actual.vs_alloca_next = encoded.vs_alloca_next /\
    window_alloca_growth initial actual /\
    actual.vs_labels = initial.vs_labels /\
    abi_encoder_registered_effect
      (window_alloca_sites func (frag_ids body_st body_end))
      [(p,32);(d,LENGTH (enc at av))] initial actual /\
    (!i b sz. i IN window_alloca_sites func (frag_ids body_st body_end) /\
      FLOOKUP actual.vs_allocas i = SOME (b,sz) ==> sz = 32) /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op encoded = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func encoded actual
Proof
  strip_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  drule_all abi_builtin_encode_finish_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) encoded = OK raw` >>
  `eval_operand buf raw = SOME (n2w p)` by metis_tac[] >>
  drule_all abi_encoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `abi_decode_sim ctx func encoded actual` >>
  `mem_bytes_at (p+32) (mid_size+len) actual.vs_memory = bytes` by
    gvs[Abbr `actual`, abi_decode_frame_def] >>
  `raw.vs_labels = encoded.vs_labels` by
    (drule_at (Pos hd)
       (Q.ISPEC `\s:venom_state. s.vs_labels` run_inst_seq_preserves_field) >>
     simp[] >> disch_then irule >> rpt strip_tac >> fs[EVERY_MEM] >>
     metis_tac[step_preserves_labels, step_inst_non_invoke]) >>
  `actual.vs_allocas = encoded.vs_allocas /\
   actual.vs_alloca_next = encoded.vs_alloca_next /\
   actual.vs_labels = encoded.vs_labels` by
    gvs[Abbr `actual`, abi_decode_frame_def] >>
  `window_alloca_growth initial actual` by
    (drule window_strong_result_growth >>
     simp[window_alloca_growth_def] >> metis_tac[]) >>
  `actual.vs_labels = initial.vs_labels` by
    metis_tac[window_strong_result_labels] >>
  `abi_decode_frame p 32 encoded actual` by
    (gvs[Abbr `actual`, abi_decode_frame_def] >> metis_tac[]) >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st final)` by
    metis_tac[abi_encode_finish_opcodes] >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  `abi_encoder_registered_effect {} [(p,32)] encoded raw` by
    (drule_all ctor_actual_scratch_free_effect >> simp[]) >>
  `abi_encoder_registered_effect {} [(p,32)] encoded actual` by
    (gvs[Abbr `actual`, abi_encoder_registered_effect_def] >> metis_tac[]) >>
  `abi_encoder_registered_effect
      (window_alloca_sites func (frag_ids body_st body_end))
      [(p,32);(d,LENGTH (enc at av))] initial actual` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `encoded` >>
     conj_tac
     >- (drule window_strong_result_effect >> strip_tac >>
         irule abi_encoder_registered_effect_enlarge >>
         goal_assum (drule_at Any) >> simp[]) >>
     irule abi_encoder_registered_effect_enlarge >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `raw` >> simp_tac bool_ss [LET_THM] >>
  qpat_x_assum `actual = raw with vs_inst_idx := _` (assume_tac o GSYM) >>
  asm_rewrite_tac[] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st final)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  gvs[markerTheory.Abbrev_def] >>
  gvs[fresh_vars_wrt_def, eval_op_inst_idx, mload_def] >>
  rpt strip_tac >> irule window_strong_result_sizes >>
  goal_assum (drule_at Any) >> gvs[] >> metis_tac[]
QED

Theorem abi_encode_allocate_opcodes[local]:
  abi_builtin_encode_allocate outsz data_offset st = (ops,address_st) ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st address_st)
Proof
  simp[abi_builtin_encode_allocate_def, compile_alloc_buffer_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem abi_encode_allocate_concrete:
  abi_builtin_encode_allocate outsz data_offset st = (ops,address_st) /\ fn_has_code st address_st func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ address_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?raw actual.
    run_inst_seq (emitted_insts st address_st) initial = OK raw /\
    actual = raw with vs_inst_idx := LENGTH address_st.cs_current_insts /\
    inst_extends st address_st /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st address_st) /\
    eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+data_offset)) /\ fresh_vars_wrt limit_st actual /\
    abi_builtin_allocation_frame st.cs_next_var st.cs_next_id outsz initial actual /\
    actual.vs_current_bb = address_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH address_st.cs_current_insts /\
    actual.vs_labels = initial.vs_labels /\
    actual.vs_accounts = initial.vs_accounts /\ actual.vs_transient = initial.vs_transient /\
    actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests /\
    actual.vs_pending_deletions = initial.vs_pending_deletions /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_allocate_shape >> strip_tac >>
  drule abi_encode_allocate_opcodes >> strip_tac >>
  drule_all abi_builtin_encode_allocate_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st address_st) initial = OK raw` >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  `~raw.vs_halted` by fs[abi_builtin_allocation_frame_def] >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`raw`, `raw with vs_inst_idx := LENGTH address_st.cs_current_insts`] >>
  gvs[abi_builtin_allocation_frame_def, fresh_vars_wrt_def, eval_op_inst_idx] >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem abi_encode_method_opcodes[local]:
  abi_builtin_encode_method_id (SOME mid) buf st = ((),final) ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st final)
Proof
  simp[abi_builtin_encode_method_id_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem abi_encode_method_concrete:
  abi_builtin_encode_method_id (SOME mid) buf st = ((),final) /\ fn_has_code st final func /\
  eval_operand buf initial = SOME (n2w p) /\ p+32 < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?raw actual.
    run_inst_seq (emitted_insts st final) initial = OK raw /\
    actual = raw with vs_inst_idx := LENGTH final.cs_current_insts /\
    inst_extends st final /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st final) /\
    mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame (p+32) 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    actual.vs_labels = initial.vs_labels /\
    actual.vs_accounts = initial.vs_accounts /\ actual.vs_transient = initial.vs_transient /\
    actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests /\
    actual.vs_pending_deletions = initial.vs_pending_deletions /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_method_shape >> strip_tac >>
  drule abi_encode_method_opcodes >> strip_tac >>
  drule_all abi_builtin_encode_method_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK raw` >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  drule abi_builtin_encode_method_window >> strip_tac >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`raw`, `raw with vs_inst_idx := LENGTH final.cs_current_insts`] >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def, eval_op_inst_idx] >>
  conj_tac >- (fs[EVERY_MEM] >> metis_tac[]) >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_method_setup_concrete:
  abi_builtin_encode_setup (SOME mid) maxlen st = (ops,ready) /\ fn_has_code st ready func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,32+32*word_size (maxlen+4))) /\
  32+32*word_size (maxlen+4) < dimword (:256) /\ p+32 < dimword (:256) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?raw actual.
    run_inst_seq (emitted_insts st ready) initial = OK raw /\
    actual = raw with vs_inst_idx := LENGTH ready.cs_current_insts /\
    inst_extends st ready /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st ready) /\
    eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+36)) /\
    mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid /\
    fresh_vars_wrt limit_st actual /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id (32+32*word_size (maxlen+4)) p 32 initial actual /\
    actual.vs_current_bb = ready.cs_current_bb /\ actual.vs_inst_idx = LENGTH ready.cs_current_insts /\
    actual.vs_labels = initial.vs_labels /\
    actual.vs_accounts = initial.vs_accounts /\ actual.vs_transient = initial.vs_transient /\
    actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests /\
    actual.vs_pending_deletions = initial.vs_pending_deletions /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_encode_method_setup_context >> strip_tac >>
  drule abi_builtin_encode_allocate_live >> strip_tac >>
  `address_st.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= address_st.cs_next_var` by decide_tac >>
  drule abi_encode_allocate_concrete >> disch_then drule >>
  disch_then (qspecl_then [`p`, `limit_st`, `initial`, `ctx`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial addressed` >>
  drule abi_encode_method_concrete >> disch_then drule >>
  disch_then (qspecl_then [`p`, `limit_st`, `addressed`, `ctx`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  rename1 `abi_decode_sim ctx func addressed actual` >>
  `actual.vs_halted = addressed.vs_halted` by simp[] >>
  `eval_operand (FST ops) actual = SOME (n2w p) /\
   eval_operand (SND ops) actual = SOME (n2w (p+36))` by
    (conj_tac >> first_x_assum irule >> asm_rewrite_tac[]) >>
  `abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id
    (32+32*word_size (maxlen+4)) p 32 initial actual` by
    (drule_all abi_builtin_encode_setup_frame_compose >> simp[]) >>
  `inst_extends st ready` by metis_tac[inst_extends_trans] >>
  `emitted_insts st ready = emitted_insts st address_st ++ emitted_insts address_st ready` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `?r. run_inst_seq (emitted_insts st ready) initial = OK r /\
    (r with vs_inst_idx := LENGTH ready.cs_current_insts) = actual` by
    (asm_rewrite_tac[] >>
     qpat_x_assum `actual = _` SUBST1_TAC >>
     irule abi_encode_run_append_normalized >>
     goal_assum (drule_at Any) >> asm_rewrite_tac[] >> metis_tac[]) >>
  qexistsl_tac [`r`, `actual`] >> asm_rewrite_tac[] >>
  conj_tac >- fs[EVERY_APPEND] >>
  irule abi_decode_sim_trans >> qexists_tac `addressed` >> metis_tac[]
QED

Theorem abi_encode_setup_none_allocate[local]:
  abi_builtin_encode_setup NONE maxlen st =
    abi_builtin_encode_allocate (32+32*word_size maxlen) 32 st
Proof
  simp[abi_builtin_encode_setup_allocate, abi_builtin_encode_method_id_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[]
QED

Theorem abi_encode_window_setup_concrete:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  fn_has_code st ready func /\
  mid_size = (case method_id of NONE => 0 | SOME mid => 4) /\
  write_size = (case method_id of NONE => 0 | SOME mid => 32) /\
  outsz = 32+32*word_size (maxlen+mid_size) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ (method_id <> NONE ==> p+32 < dimword (:256)) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_window_input ei at av sb cap initial.vs_memory /\
  (sb+cap <= p+32 \/ p+32+write_size <= sb) ==>
  ?raw.
    run_inst_seq (emitted_insts st ready) initial = OK raw /\
    inst_extends st ready /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st ready) /\
    let actual = raw with vs_inst_idx := LENGTH ready.cs_current_insts in
    eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+32+mid_size)) /\
    fresh_vars_wrt limit_st actual /\
    FLOOKUP actual.vs_allocas st.cs_next_id = SOME (p,outsz) /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p write_size initial actual /\
    abi_encoder_window_input ei at av sb cap actual.vs_memory /\
    (case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid) /\
    actual.vs_current_bb = ready.cs_current_bb /\
    actual.vs_inst_idx = LENGTH ready.cs_current_insts /\
    actual.vs_labels = initial.vs_labels /\
    actual.vs_accounts = initial.vs_accounts /\ actual.vs_transient = initial.vs_transient /\
    actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests /\
    actual.vs_pending_deletions = initial.vs_pending_deletions /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  Cases_on `method_id` >> simp[] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `mid_size = _` SUBST_ALL_TAC >>
  qpat_x_assum `write_size = _` SUBST_ALL_TAC >>
  qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
  rule_assum_tac (SRULE [])
  >- (qpat_x_assum `abi_builtin_encode_setup NONE _ _ = _`
        (assume_tac o REWRITE_RULE [abi_encode_setup_none_allocate]) >>
      drule abi_encode_allocate_concrete >> disch_then drule >>
      disch_then (qspecl_then [`p`, `limit_st`, `initial`, `ctx`] mp_tac) >>
      (impl_tac >- (pure_rewrite_tac[Q.SPECL [`32`, `32*word_size maxlen`] ADD_COMM] >>
        asm_rewrite_tac[])) >> strip_tac >>
      `abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id
         (32+32*word_size maxlen) p 0 initial actual` by
        gvs[abi_builtin_encode_setup_frame_def, abi_builtin_allocation_frame_def,
          abi_decode_frame_def] >>
      `FLOOKUP actual.vs_allocas st.cs_next_id = SOME (p,32+32*word_size maxlen)` by
        (irule abi_builtin_encode_setup_frame_row >> goal_assum (drule_at Any) >> simp[]) >>
      `abi_encoder_window_input ei at av sb cap actual.vs_memory` by
        (irule abi_encode_setup_frame_window_input >>
         goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
      qexists_tac `raw` >>
      pure_rewrite_tac[Q.SPECL [`32*word_size maxlen`, `32`] ADD_COMM] >> gvs[]) >>
  drule abi_encode_method_setup_concrete >> disch_then drule >>
  disch_then (qspecl_then [`p`, `limit_st`, `initial`, `ctx`] mp_tac) >>
  (impl_tac >- (pure_rewrite_tac[Q.SPECL [`32`, `32*word_size (maxlen+4)`] ADD_COMM] >>
    asm_rewrite_tac[])) >> strip_tac >>
  `FLOOKUP actual.vs_allocas st.cs_next_id = SOME (p,32+32*word_size (maxlen+4))` by
    (irule abi_builtin_encode_setup_frame_row >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_encoder_window_input ei at av sb cap actual.vs_memory` by
    (irule abi_encode_setup_frame_window_input >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  qexists_tac `raw` >>
  pure_rewrite_tac[Q.SPECL [`32*word_size (maxlen+4)`, `32`] ADD_COMM] >> gvs[]
QED
