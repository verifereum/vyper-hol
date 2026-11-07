Theory exprSimAbiEncodeFramedBuiltin
Ancestors
  exprSimAbiEncodeFramedLeaves abiEncodeWindowBuiltin
  abiBuiltinEncodeCorrect abiEncoderWindowContract abiDecoderContract
  abiBuiltinEncodeCode abiDecoderEffect valueEncoding venomState finite_map words
  ctorAbiActualObservations ctorAbiActualWorld abiDecoderReentry emitHelper
  abiEncoderRegisteredEffect abiEncoderSequence abiDecoderLoop instIdxIndep
  exprLoweringProps venomInst list rich_list arithmetic compileEnv abiDecoderVarSequence
  abiBuiltinEncodeMethod abiBuiltinEncodeSetup abiBuiltinAllocation abiEncoderInput
  venomMemDefs abiEncoderOpenInput abiEncoderWindow abiBuiltinEncodeAllocate context
  abiEncoderWindowLookup abiEncoderWindowSequence exprSimAbiEncodeExecFrame
  venomInstProofs1 venomExecSemantics intCallCallee moduleLoweringProps fragExec
  exprSimAbiEncodeSemantic stmtSimLogExecFields exprSimAbiEncodeMemoryLength

Theorem abi_encode_leaf_sequence_context:
  run_inst_seq code s = OK t /\
  EVERY (\i. ~is_terminator i.inst_opcode) code ==>
  (t.vs_call_ctx,t.vs_data_section) = (s.vs_call_ctx,s.vs_data_section)
Proof
  strip_tac >> irule (BETA_RULE (Q.ISPEC
    `\s:venom_state. (s.vs_call_ctx,s.vs_data_section)` run_inst_seq_preserves_field)) >>
  qexists_tac `code` >> simp[] >> rpt strip_tac >>
  `~is_terminator i.inst_opcode` by
    (fs[EVERY_MEM] >> first_x_assum irule >> simp[]) >>
  drule_all step_inst_base_preserves_all >> simp[]
QED

Theorem abi_encode_framed_finish_opcodes:
  abi_builtin_encode_finish buf encoded_len mid_size st = ((),final) ==>
  EVERY (\i. MEM i.inst_opcode [ADD;MSTORE]) (emitted_insts st final)
Proof
  Cases_on `mid_size > 0` >>
  simp[abi_builtin_encode_finish_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
    emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encode_framed_finish_sequence:
  abi_builtin_encode_finish buf encoded_len mid_size st = ((),final) /\
  run_inst_seq (emitted_insts st final) s = OK t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next ==>
  abi_encode_exec_frame func s t
Proof
  strip_tac >> drule abi_encode_framed_finish_opcodes >> strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [ADD;AND;MLOAD;MSTORE;MCOPY]) (emitted_insts st final)` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st final)` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i _ ==> i.inst_opcode = ADD \/ i.inst_opcode = MSTORE`
       drule >> strip_tac >> gvs[is_terminator_def]) >>
  drule_all abi_encode_leaf_sequence_fmp >> strip_tac >>
  drule_all abi_encode_leaf_sequence_semantic >> strip_tac >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    (irule abi_encode_leaf_sequence_memory_length >>
     qexists_tac `emitted_insts st final` >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all abi_encode_leaf_sequence_context >>
  simp[abi_encode_exec_frame_def, pending_alloca_size_def]
QED

Theorem abi_encode_framed_finish_reach:
  abi_builtin_encode_finish buf encoded_len mid_size st = ((),final) /\
  fn_has_code st final func /\
  eval_operand buf initial = SOME (n2w p) /\
  eval_operand encoded_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var buf /\
  p < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand buf actual = SOME (n2w p) /\
    mload p actual = n2w (len+mid_size) /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame p 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_labels = initial.vs_labels /\
    abi_encoder_registered_effect {} [(p,32)] initial actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\
    abi_encode_exec_frame func initial actual
Proof
  strip_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  drule abi_encode_framed_finish_opcodes >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st final)` by
    (fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >>
     simp[abi_decoder_reentry_opcode_def] >> metis_tac[]) >>
  drule_all abi_builtin_encode_finish_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK encoded` >>
  `abi_encode_exec_frame func initial encoded` by
    (drule_all abi_encode_framed_finish_sequence >> simp[]) >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  `abi_encoder_registered_effect {} [(p,32)] initial encoded` by
    (drule_all ctor_actual_scratch_free_effect >> simp[]) >>
  `eval_operand buf encoded = SOME (n2w p)` by
    (first_x_assum irule >> simp[]) >>
  drule_all abi_encoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH final.cs_current_insts` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def, eval_op_inst_idx, mload_def,
    abi_encoder_registered_effect_def] >> metis_tac[]
QED

Theorem abi_encode_framed_builtin_finish:
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
  ?actual.
    eval_operand buf actual = SOME (n2w p) /\
    mload p actual = n2w (len+mid_size) /\
    mem_bytes_at (p+32) (mid_size+len) actual.vs_memory = bytes /\
    fresh_vars_wrt limit_st actual /\
    abi_decode_frame p 32 encoded actual /\
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
    ~actual.vs_halted /\ abi_decode_sim ctx func encoded actual /\
    abi_encode_exec_frame func encoded actual
Proof
  strip_tac >>
  drule_all abi_encode_framed_finish_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `mem_bytes_at (p+32) (mid_size+len) actual.vs_memory = bytes` by
    (gvs[abi_decode_frame_def]) >>
  `window_alloca_growth initial actual` by
    (drule window_strong_result_growth >>
     simp[window_alloca_growth_def] >> metis_tac[]) >>
  `actual.vs_labels = initial.vs_labels` by
    metis_tac[window_strong_result_labels] >>
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
  qexists_tac `actual` >> simp[] >>
  rpt strip_tac >> irule window_strong_result_sizes >>
  goal_assum (drule_at Any) >> gvs[] >> metis_tac[]
QED

Theorem abi_encode_setup_step_fmp:
  MEM inst.inst_opcode [ALLOCA;ADD;MSTORE] /\ step_inst_base inst s = OK t ==>
  t.vs_fmp = s.vs_fmp
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      simp[Once step_inst_base_def] >>
      simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[update_var_def]) >>
  irule step_inst_base_preserves_fmp_ordinary >> qexists_tac `inst` >>
  fs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def] >>
  rpt strip_tac >> gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def]
QED

Theorem abi_encode_setup_sequence_fmp:
  run_inst_seq code s = OK t /\
  EVERY (\i. MEM i.inst_opcode [ALLOCA;ADD;MSTORE]) code ==>
  t.vs_fmp = s.vs_fmp
Proof
  strip_tac >> irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_fmp`
    run_inst_seq_preserves_field)) >> qexists_tac `code` >> simp[] >>
  rpt strip_tac >> irule abi_encode_setup_step_fmp >>
  qexists_tac `i` >> simp[] >> fs[EVERY_MEM]
QED

Theorem abi_encode_setup_sequence_world:
  run_inst_seq code s = OK t /\
  EVERY (\i. MEM i.inst_opcode [ALLOCA;ADD;MSTORE]) code ==>
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
  t.vs_pending_deletions = s.vs_pending_deletions
Proof
  strip_tac >>
  `log_encode_external t = log_encode_external s` by
    (irule log_encode_run_external >> qexists `code` >> simp[] >>
     fs[EVERY_MEM, log_encode_safe_opcode_def] >> metis_tac[]) >>
  drule log_encode_external_fields >> simp[]
QED

Theorem abi_encode_emitted_instruction_member:
  fn_has_code st final func /\ MEM inst (emitted_insts st final) ==>
  MEM inst (fn_insts func)
Proof
  strip_tac >> gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  gvs[emitted_insts_def, MEM_APPEND] >> metis_tac[MEM_DROP_IMP]
QED

Theorem abi_encode_setup_sequence_frame:
  fn_has_code st final func /\
  run_inst_seq (emitted_insts st final) s = OK t /\
  EVERY (\i. MEM i.inst_opcode [ALLOCA;ADD;MSTORE]) (emitted_insts st final) ==>
  abi_encode_exec_frame func s t
Proof
  strip_tac >>
  `EVERY (\i. MEM i (fn_insts func) /\ i.inst_opcode <> INVOKE)
    (emitted_insts st final)` by
    (fs[EVERY_MEM] >> rpt strip_tac >-
      (irule abi_encode_emitted_instruction_member >> goal_assum (drule_at Any) >> simp[]) >>
     first_x_assum drule >> simp[] >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st final)` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i _ ==> i.inst_opcode = ALLOCA \/ _`
       drule >> strip_tac >> gvs[is_terminator_def]) >>
  drule_all run_inst_seq_static_charge >> strip_tac >>
  drule_all abi_encode_setup_sequence_fmp >> strip_tac >>
  `abi_encode_semantic_obs t = abi_encode_semantic_obs s` by
    (irule abi_encode_semantic_sequence >> goal_assum (drule_at Any) >>
     gvs[EVERY_MEM, log_encode_safe_opcode_def] >> metis_tac[]) >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    (irule abi_encode_leaf_sequence_memory_length >>
     qexists_tac `emitted_insts st final` >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all abi_encode_leaf_sequence_context >> simp[abi_encode_exec_frame_def]
QED

Theorem abi_encode_framed_allocate_opcodes:
  abi_builtin_encode_allocate outsz offset st = (ops,final) ==>
  EVERY (\i. MEM i.inst_opcode [ALLOCA;ADD;MSTORE]) (emitted_insts st final)
Proof
  simp[abi_builtin_encode_allocate_def, compile_alloc_buffer_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def,
    emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encode_framed_setup_none_opcodes:
  abi_builtin_encode_setup NONE maxlen st = (ops,final) ==>
  EVERY (\i. MEM i.inst_opcode [ALLOCA;ADD;MSTORE]) (emitted_insts st final)
Proof
  simp[abi_builtin_encode_setup_allocate, abi_builtin_encode_method_id_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  drule abi_encode_framed_allocate_opcodes >> simp[]
QED

Theorem abi_encode_framed_allocate_reach:
  abi_builtin_encode_allocate outsz data_offset st = (ops,address_st) /\ fn_has_code st address_st func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ address_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+data_offset)) /\ fresh_vars_wrt limit_st actual /\
    abi_builtin_allocation_frame st.cs_next_var st.cs_next_id outsz initial actual /\
    actual.vs_current_bb = address_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH address_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\
    abi_encode_exec_frame func initial actual /\
    actual.vs_accounts = initial.vs_accounts /\ actual.vs_transient = initial.vs_transient /\
    actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests /\
    actual.vs_pending_deletions = initial.vs_pending_deletions
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_allocate_shape >> strip_tac >>
  drule abi_encode_framed_allocate_opcodes >> strip_tac >>
  drule_all abi_builtin_encode_allocate_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st address_st) initial = OK encoded` >>
  drule_all abi_encode_setup_sequence_world >> strip_tac >>
  `abi_encode_exec_frame func initial encoded` by
    (drule_all abi_encode_setup_sequence_frame >> simp[]) >>
  `~encoded.vs_halted` by fs[abi_builtin_allocation_frame_def] >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH address_st.cs_current_insts` >>
  gvs[abi_builtin_allocation_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem abi_encode_framed_setup_none_reach:
  abi_builtin_encode_setup NONE maxlen st = (ops,ready) /\ fn_has_code st ready func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,32+32*word_size maxlen)) /\
  32+32*word_size maxlen < dimword (:256) /\ ready.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+32)) /\
    fresh_vars_wrt limit_st actual /\
    abi_builtin_allocation_frame st.cs_next_var st.cs_next_id (32+32*word_size maxlen) initial actual /\
    actual.vs_current_bb = ready.cs_current_bb /\ actual.vs_inst_idx = LENGTH ready.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\
    abi_encode_exec_frame func initial actual /\
    actual.vs_accounts = initial.vs_accounts /\ actual.vs_transient = initial.vs_transient /\
    actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests /\
    actual.vs_pending_deletions = initial.vs_pending_deletions
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_encode_framed_setup_none_opcodes >> strip_tac >>
  drule_all abi_builtin_encode_setup_none_execute >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) initial = OK encoded` >>
  drule_all abi_encode_setup_sequence_world >> strip_tac >>
  `abi_encode_exec_frame func initial encoded` by
    (drule_all abi_encode_setup_sequence_frame >> simp[]) >>
  `~encoded.vs_halted` by fs[abi_builtin_allocation_frame_def] >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH ready.cs_current_insts` >>
  gvs[abi_builtin_allocation_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem abi_encode_framed_method_opcodes:
  abi_builtin_encode_method_id (SOME mid) buf st = ((),final) ==>
  EVERY (\i. MEM i.inst_opcode [ALLOCA;ADD;MSTORE]) (emitted_insts st final)
Proof
  simp[abi_builtin_encode_method_id_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encode_framed_method_reach:
  abi_builtin_encode_method_id (SOME mid) buf st = ((),final) /\ fn_has_code st final func /\
  eval_operand buf initial = SOME (n2w p) /\ p+32 < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame (p+32) 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\
    abi_encode_exec_frame func initial actual /\
    actual.vs_accounts = initial.vs_accounts /\ actual.vs_transient = initial.vs_transient /\
    actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests /\
    actual.vs_pending_deletions = initial.vs_pending_deletions
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_method_shape >> strip_tac >>
  drule abi_encode_framed_method_opcodes >> strip_tac >>
  drule_all abi_builtin_encode_method_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK encoded` >>
  drule_all abi_encode_setup_sequence_world >> strip_tac >>
  `abi_encode_exec_frame func initial encoded` by
    (drule_all abi_encode_setup_sequence_frame >> simp[]) >>
  drule abi_builtin_encode_method_window >> strip_tac >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH final.cs_current_insts` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def, eval_op_inst_idx] >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_framed_setup_some_reach:
  abi_builtin_encode_setup (SOME mid) maxlen st = (ops,ready) /\ fn_has_code st ready func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,32+32*word_size (maxlen+4))) /\
  32+32*word_size (maxlen+4) < dimword (:256) /\ p+32 < dimword (:256) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+36)) /\
    mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid /\
    fresh_vars_wrt limit_st actual /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id (32+32*word_size (maxlen+4)) p 32 initial actual /\
    actual.vs_current_bb = ready.cs_current_bb /\ actual.vs_inst_idx = LENGTH ready.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual /\
    abi_encode_exec_frame func initial actual /\
    actual.vs_accounts = initial.vs_accounts /\ actual.vs_transient = initial.vs_transient /\
    actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests /\
    actual.vs_pending_deletions = initial.vs_pending_deletions
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_encode_method_setup_context >> strip_tac >>
  drule abi_builtin_encode_allocate_live >> strip_tac >>
  `address_st.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= address_st.cs_next_var` by decide_tac >>
  drule_all abi_encode_framed_allocate_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial addressed` >>
  drule_all abi_encode_framed_method_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func addressed actual` >>
  `actual.vs_halted = addressed.vs_halted` by simp[] >>
  `eval_operand (FST ops) actual = SOME (n2w p) /\
   eval_operand (SND ops) actual = SOME (n2w (p+36))` by
    (conj_tac >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id (32+32*word_size (maxlen+4)) p 32 initial actual` by
    (drule_all abi_builtin_encode_setup_frame_compose >> simp[]) >>
  `abi_encode_exec_frame func initial actual` by
    (irule abi_encode_exec_frame_trans >> qexists_tac `addressed` >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `addressed` >> asm_simp_tac bool_ss []
QED
