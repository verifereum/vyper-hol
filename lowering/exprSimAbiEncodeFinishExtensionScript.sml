Theory exprSimAbiEncodeFinishExtension
Ancestors
  abiEncodeWindowBuiltin abiEncoderExtendSim abiBuiltinEncodeCode abiBuiltinEncodeCorrect venomState
  abiEncoderWindowContract abiDecoderContract abiDecoderReentry
  abiEncoderRegisteredEffect abiEncoderSequence abiDecoderLoop instIdxIndep
  ctorAbiActualObservations ctorAbiActualWorld abiDecoderVarSequence
  exprLoweringProps venomInst list rich_list arithmetic compileEnv emitHelper
  abiBuiltinEncodeMethod abiBuiltinEncodeSetup abiBuiltinAllocation abiEncoderInput
  venomMemDefs abiEncoderOpenInput abiEncoderWindow abiBuiltinEncodeAllocate context
  abiEncoderWindowLookup abiEncoderWindowSequence entrySinkExtraction

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

Theorem abi_encode_finish_reach_extend[local]:
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
    abi_encoder_extend_sim ctx func initial actual
Proof
  disch_then strip_assume_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  drule abi_encode_finish_opcodes >> strip_tac >>
  drule_all abi_builtin_encode_finish_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK encoded` >>
  drule_all ctor_actual_sequence_world >> strip_tac >>
  drule_all ctor_actual_sequence_labels >> strip_tac >>
  `abi_encoder_registered_effect {} [(p,32)] initial encoded` by
    (drule_all ctor_actual_scratch_free_effect >> simp[]) >>
  `eval_operand buf encoded = SOME (n2w p)` by
    (first_x_assum irule >> simp[]) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  drule_all abi_encoder_run_sequence_extend_sim >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_encoder_extend_sim_sim >> strip_tac >>
  qexists_tac `encoded with vs_inst_idx := LENGTH final.cs_current_insts` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def, eval_op_inst_idx, mload_def,
    abi_encoder_registered_effect_def] >> metis_tac[]
QED

Theorem abi_encode_window_finish_extend:
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
    abi_encoder_extend_sim ctx func encoded actual
Proof
  disch_then strip_assume_tac >>
  drule_all abi_encode_finish_reach_extend >>
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
