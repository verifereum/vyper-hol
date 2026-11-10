Theory abiEncodeWindowBuiltin
Ancestors
  abiBuiltinEncodeCorrect abiEncoderWindowContract abiDecoderContract
  abiBuiltinEncodeCode abiDecoderEffect valueEncoding venomState finite_map words
  ctorAbiActualObservations ctorAbiActualWorld abiDecoderReentry emitHelper
  abiEncoderRegisteredEffect abiEncoderSequence abiDecoderLoop instIdxIndep
  exprLoweringProps venomInst list rich_list arithmetic compileEnv abiDecoderVarSequence
  abiBuiltinEncodeMethod abiBuiltinEncodeSetup abiBuiltinAllocation abiEncoderInput
  venomMemDefs abiEncoderOpenInput abiEncoderWindow abiBuiltinEncodeAllocate context
  abiEncoderWindowLookup abiEncoderWindowSequence
  loweringStateRelDefs
Theorem abi_window_finish_opcodes[local]:
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

Theorem abi_window_finish_reach[local]:
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
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then strip_assume_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  drule abi_window_finish_opcodes >> strip_tac >>
  drule_all abi_builtin_encode_finish_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK encoded` >>
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

(* The finish store is outside the completed payload.  No interval allocation
   budget is needed: its allocation map and frontier are unchanged. *)
Theorem abi_window_builtin_finish:
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
    ~actual.vs_halted /\ abi_decode_sim ctx func encoded actual
Proof
  disch_then strip_assume_tac >>
  drule_all abi_window_finish_reach >>
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

(* A uniform setup interface; write_size is the physical method-id store,
   whereas mid_size is the logical four-byte selector prefix. *)
Theorem abi_window_builtin_setup:
  abi_builtin_encode_setup method_id maxlen st = (ops,ready) /\
  fn_has_code st ready func /\
  mid_size = (case method_id of NONE => 0 | SOME mid => 4) /\
  write_size = (case method_id of NONE => 0 | SOME mid => 32) /\
  outsz = 32+32*word_size (maxlen+mid_size) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  outsz < dimword (:256) /\ p+32 < dimword (:256) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  abi_encoder_input ei at av sb cap initial.vs_memory /\
  (sb+cap <= p+32 \/ p+32+write_size <= sb) ==>
  ?actual.
    eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+32+mid_size)) /\
    fresh_vars_wrt limit_st actual /\
    FLOOKUP actual.vs_allocas st.cs_next_id = SOME (p,outsz) /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p write_size initial actual /\
    abi_encoder_input ei at av sb cap actual.vs_memory /\
    (case method_id of NONE => T | SOME mid =>
      mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid) /\
    actual.vs_current_bb = ready.cs_current_bb /\
    actual.vs_inst_idx = LENGTH ready.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  Cases_on `method_id` >> simp[] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `mid_size = _` SUBST_ALL_TAC >>
  qpat_x_assum `write_size = _` SUBST_ALL_TAC >>
  qpat_x_assum `outsz = _` SUBST_ALL_TAC >>
  rule_assum_tac (SRULE [])
  >- (drule abi_builtin_encode_setup_none_reach >>
      disch_then drule >>
      disch_then (qspecl_then [`p`, `limit_st`, `initial`, `ctx`] mp_tac) >>
      (impl_tac >- (pure_rewrite_tac[Q.SPECL [`32`, `32*word_size maxlen`] ADD_COMM] >>
        asm_rewrite_tac[])) >> strip_tac >>
      `abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id
         (32+32*word_size maxlen) p 0 initial actual` by
        gvs[abi_builtin_encode_setup_frame_def, abi_builtin_allocation_frame_def,
          abi_decode_frame_def] >>
      `FLOOKUP actual.vs_allocas st.cs_next_id =
         SOME (p,32+32*word_size maxlen)` by
        (irule abi_builtin_encode_setup_frame_row >> goal_assum (drule_at Any) >> simp[]) >>
      `abi_encoder_input ei at av sb cap actual.vs_memory` by
        (irule abi_builtin_encode_setup_frame_input >>
         goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
      qexists_tac `actual` >>
      pure_rewrite_tac[Q.SPECL [`32*word_size maxlen`, `32`] ADD_COMM] >> simp[]) >>
  drule abi_builtin_encode_method_setup_reach >> disch_then drule >>
  disch_then (qspecl_then [`p`, `limit_st`, `initial`, `ctx`] mp_tac) >>
  (impl_tac >- (pure_rewrite_tac[Q.SPECL [`32`, `32*word_size (maxlen+4)`] ADD_COMM] >>
    asm_rewrite_tac[])) >> strip_tac >>
  `FLOOKUP actual.vs_allocas st.cs_next_id =
     SOME (p,32+32*word_size (maxlen+4))` by
    (irule abi_builtin_encode_setup_frame_row >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_encoder_input ei at av sb cap actual.vs_memory` by
    (irule abi_builtin_encode_setup_frame_input >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  qexists_tac `actual` >>
  pure_rewrite_tac[Q.SPECL [`32*word_size (maxlen+4)`, `32`] ADD_COMM] >> simp[]
QED

(* Resource transport is relative to the pure allocated state, not a claim
   that allocation itself establishes room or non-overlap. *)
Theorem abi_window_setup_allocas:
  abi_builtin_encode_setup_frame next site outsz p write_size s t ==>
  t.vs_allocas = (abi_builtin_allocate_state site outsz s).vs_allocas
Proof
  simp[abi_builtin_encode_setup_frame_def]
QED

Theorem abi_window_setup_frontier:
  abi_builtin_encode_setup_frame next site outsz p write_size s t ==>
  t.vs_alloca_next = (abi_builtin_allocate_state site outsz s).vs_alloca_next
Proof
  simp[abi_builtin_encode_setup_frame_def]
QED

Theorem abi_window_setup_room:
  abi_builtin_encode_setup_frame next site outsz p write_size s t ==>
  (alloca_room ctx func t <=>
   alloca_room ctx func (abi_builtin_allocate_state site outsz s))
Proof
  strip_tac >> drule abi_window_setup_allocas >>
  drule abi_window_setup_frontier >>
  simp[alloca_room_def, pending_alloca_size_def]
QED

Theorem abi_window_setup_alloca_inv:
  abi_builtin_encode_setup_frame next site outsz p write_size s t ==>
  (alloca_inv t <=> alloca_inv (abi_builtin_allocate_state site outsz s))
Proof
  strip_tac >> drule abi_window_setup_allocas >>
  drule abi_window_setup_frontier >>
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

(* This conversion is semantic, not an inference of declared capacity from a
   source footprint.  Callers must already supply the encoder input. *)
Theorem abi_window_setup_input:
  abi_builtin_encode_setup_frame next site outsz p write_size s t /\
  abi_encoder_input ei at av sb cap s.vs_memory /\
  (sb+cap <= p+32 \/ p+32+write_size <= sb) ==>
  abi_encoder_window_input ei at av sb cap t.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_encoder_input ei at av sb cap t.vs_memory` by
    (irule abi_builtin_encode_setup_frame_input >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  metis_tac[abi_encoder_input_open, abi_encoder_open_input_window]
QED

Theorem abi_window_setup_zero_probe[local]:
  32+32*word_size 0 = 32 /\
  64 <= 32+32*word_size (0+4) /\
  (!p. p+32 = dimword (:256) ==> ~(p+32 < dimword (:256)))
Proof
  simp[abi_builtin_rounded_capacity_checks]
QED

Theorem abi_window_allocate_opcodes[local]:
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

Theorem abi_window_allocate_observed_reach:
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
    actual.vs_labels = initial.vs_labels /\
    actual.vs_accounts = initial.vs_accounts /\ actual.vs_transient = initial.vs_transient /\
    actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests /\
    actual.vs_pending_deletions = initial.vs_pending_deletions /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_allocate_shape >> strip_tac >>
  drule abi_window_allocate_opcodes >> strip_tac >>
  drule_all abi_builtin_encode_allocate_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st address_st) initial = OK encoded` >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  `~encoded.vs_halted` by fs[abi_builtin_allocation_frame_def] >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH address_st.cs_current_insts` >>
  gvs[abi_builtin_allocation_frame_def, fresh_vars_wrt_def, eval_op_inst_idx]
QED

Theorem abi_window_method_opcodes[local]:
  abi_builtin_encode_method_id (SOME mid) buf st = ((),final) ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st final)
Proof
  simp[abi_builtin_encode_method_id_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Theorem abi_window_method_observed_reach:
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
    actual.vs_labels = initial.vs_labels /\
    actual.vs_accounts = initial.vs_accounts /\ actual.vs_transient = initial.vs_transient /\
    actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests /\
    actual.vs_pending_deletions = initial.vs_pending_deletions /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_method_shape >> strip_tac >>
  drule abi_window_method_opcodes >> strip_tac >>
  drule_all abi_builtin_encode_method_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK encoded` >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  drule abi_builtin_encode_method_window >> strip_tac >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH final.cs_current_insts` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def, eval_op_inst_idx] >> first_assum ACCEPT_TAC
QED

Theorem abi_window_method_setup_observed_reach:
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
  drule abi_window_allocate_observed_reach >> disch_then drule >>
  disch_then (qspecl_then [`p`, `limit_st`, `initial`, `ctx`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial addressed` >>
  drule abi_window_method_observed_reach >> disch_then drule >>
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
  qexists_tac `actual` >> asm_rewrite_tac[] >>
  irule abi_decode_sim_trans >> qexists_tac `addressed` >> asm_rewrite_tac[]
QED

Theorem abi_window_setup_none_allocate[local]:
  abi_builtin_encode_setup NONE maxlen st =
    abi_builtin_encode_allocate (32+32*word_size maxlen) 32 st
Proof
  simp[abi_builtin_encode_setup_allocate, abi_builtin_encode_method_id_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[]
QED

Theorem abi_window_builtin_setup_observed:
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
  abi_encoder_input ei at av sb cap initial.vs_memory /\
  (sb+cap <= p+32 \/ p+32+write_size <= sb) ==>
  ?actual.
    eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+32+mid_size)) /\
    fresh_vars_wrt limit_st actual /\
    FLOOKUP actual.vs_allocas st.cs_next_id = SOME (p,outsz) /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p write_size initial actual /\
    abi_encoder_input ei at av sb cap actual.vs_memory /\
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
        (assume_tac o REWRITE_RULE [abi_window_setup_none_allocate]) >>
      drule abi_window_allocate_observed_reach >> disch_then drule >>
      disch_then (qspecl_then [`p`, `limit_st`, `initial`, `ctx`] mp_tac) >>
      (impl_tac >- (pure_rewrite_tac[Q.SPECL [`32`, `32*word_size maxlen`] ADD_COMM] >>
        asm_rewrite_tac[])) >> strip_tac >>
      `abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id
         (32+32*word_size maxlen) p 0 initial actual` by
        gvs[abi_builtin_encode_setup_frame_def, abi_builtin_allocation_frame_def,
          abi_decode_frame_def] >>
      `FLOOKUP actual.vs_allocas st.cs_next_id = SOME (p,32+32*word_size maxlen)` by
        (irule abi_builtin_encode_setup_frame_row >> goal_assum (drule_at Any) >> simp[]) >>
      `abi_encoder_input ei at av sb cap actual.vs_memory` by
        (irule abi_builtin_encode_setup_frame_input >>
         goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
      qexists_tac `actual` >>
      pure_rewrite_tac[Q.SPECL [`32*word_size maxlen`, `32`] ADD_COMM] >> simp[]) >>
  drule abi_window_method_setup_observed_reach >> disch_then drule >>
  disch_then (qspecl_then [`p`, `limit_st`, `initial`, `ctx`] mp_tac) >>
  (impl_tac >- (pure_rewrite_tac[Q.SPECL [`32`, `32*word_size (maxlen+4)`] ADD_COMM] >>
    asm_rewrite_tac[])) >> strip_tac >>
  `FLOOKUP actual.vs_allocas st.cs_next_id = SOME (p,32+32*word_size (maxlen+4))` by
    (irule abi_builtin_encode_setup_frame_row >> goal_assum (drule_at Any) >> simp[]) >>
  `abi_encoder_input ei at av sb cap actual.vs_memory` by
    (irule abi_builtin_encode_setup_frame_input >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  qexists_tac `actual` >>
  pure_rewrite_tac[Q.SPECL [`32*word_size (maxlen+4)`, `32`] ADD_COMM] >> simp[]
QED

Theorem abi_window_allocate_other_row:
  id <> site ==>
  FLOOKUP (abi_builtin_allocate_state site outsz s).vs_allocas id =
    FLOOKUP s.vs_allocas id
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas site = NONE` >>
  simp[abi_builtin_allocate_state_def, FLOOKUP_UPDATE]
QED

Theorem abi_window_allocate_reused:
  FLOOKUP s.vs_allocas site = SOME row ==>
  abi_builtin_allocate_state site outsz s = s
Proof
  simp[abi_builtin_allocate_state_def]
QED

Theorem abi_window_fresh_vars_fields:
  t.vs_vars = s.vs_vars /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st t
Proof
  simp[fresh_vars_wrt_def]
QED

Theorem abi_window_empty_sequence_fresh[local]:
  run_inst_seq [] s = OK t /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st t
Proof
  simp[run_inst_seq_def] >> metis_tac[]
QED
