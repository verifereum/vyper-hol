Theory abiEncodeWindowBuiltin
Ancestors
  abiBuiltinEncodeCorrect abiEncoderWindowContract abiDecoderContract
  abiBuiltinEncodeCode abiDecoderEffect valueEncoding venomState finite_map words
  ctorAbiActualObservations ctorAbiActualWorld abiDecoderReentry emitHelper
  abiEncoderRegisteredEffect abiEncoderSequence abiDecoderLoop instIdxIndep
  exprLoweringProps venomInst list rich_list arithmetic compileEnv abiDecoderVarSequence
  abiBuiltinEncodeMethod abiBuiltinEncodeSetup abiBuiltinAllocation abiEncoderInput
  venomMemDefs

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
