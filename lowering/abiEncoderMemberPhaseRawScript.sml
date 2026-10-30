(* Early concrete member endpoints: no legacy member invariant owners. *)
Theory abiEncoderMemberPhaseRaw
Ancestors
  abiEncoderChildSuffix abiEncoderChildPrefix abiDecoderFrame abiEncoderArrayTail abiBuiltinPrefix
  abiEncoderExtendSim abiEncoderAddressReach emitHelperProps emitHelper venomInst
  abiDecoderReentryAddress abiDecoderReentry abiDecoderDynamicLoopSetup
  abiDecoderContract abiDecoderLoop fragExec compileEnv venomState
  venomExecSemantics venomInstProps exprLoweringProps abiEncoderChildCode
  instIdxIndep words list

Definition abi_encoder_member_phase_raw_def:
  abi_encoder_member_phase_raw st final initial ready <=>
    ?u. run_inst_seq (emitted_insts st final) initial = OK u /\
        ready = (u with vs_inst_idx := LENGTH final.cs_current_insts)
End

Theorem abi_encoder_member_binary_raw:
  emit_op opc [lhs;rhs] st = (out,final) /\ (opc = ADD \/ opc = MUL) /\
  eval_operand lhs initial = SOME a /\ eval_operand rhs initial = SOME b /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?ready. abi_encoder_member_phase_raw st final initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_binary_reentry >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH final.cs_current_insts` >>
  simp[abi_encoder_member_phase_raw_def] >> qexists_tac `t` >> simp[]
QED

Theorem abi_encoder_member_binary_transport:
  emit_op opc [lhs;rhs] st = (out,final) /\ (opc = ADD \/ opc = MUL) /\
  eval_operand lhs initial = SOME a /\ eval_operand rhs initial = SOME b /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  eval_operand out ready = SOME (if opc = ADD then a+b else a*b) /\
  fresh_vars_wrt limit_st ready /\ abi_decoder_address_frame st.cs_next_var initial ready /\
  ready.vs_current_bb = initial.vs_current_bb /\
  ready.vs_inst_idx = LENGTH final.cs_current_insts /\
  ready.vs_halted = initial.vs_halted
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_binary_reentry >> strip_tac >>
  gvs[abi_encoder_member_phase_raw_def] >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx,
      update_var_def]
QED

Theorem abi_encoder_member_load_raw:
  emit_op MLOAD [src] st = (out,final) /\ eval_operand src initial = SOME p /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?ready. abi_encoder_member_phase_raw st final initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`opc` |-> `MLOAD`, `s` |-> `initial:venom_state`, `st'` |-> `final:compile_state`] abi_decoder_read_reentry) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_decode_source_opcode_def] >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH final.cs_current_insts` >>
  simp[abi_encoder_member_phase_raw_def] >> qexists_tac `t` >> simp[]
QED

Theorem abi_encoder_member_load_transport:
  emit_op MLOAD [src] st = (out,final) /\ eval_operand src initial = SOME p /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  eval_operand out ready = SOME (mload (w2n p) initial) /\
  fresh_vars_wrt limit_st ready /\ abi_decoder_address_frame st.cs_next_var initial ready /\
  ready.vs_current_bb = initial.vs_current_bb /\
  ready.vs_inst_idx = LENGTH final.cs_current_insts /\
  ready.vs_halted = initial.vs_halted
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`opc` |-> `MLOAD`, `s` |-> `initial:venom_state`, `st'` |-> `final:compile_state`] abi_decoder_read_reentry) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_decode_source_opcode_def] >> strip_tac >>
  gvs[abi_encoder_member_phase_raw_def] >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx,
      abi_decode_load_def, update_var_def]
QED

Theorem abi_encoder_member_cursor_raw:
  abi_encode_child_suffix head dyn_ptr offset child_len st = (out,final) /\
  eval_operand head initial = SOME (n2w h) /\ eval_operand dyn_ptr initial = SOME (n2w p) /\
  eval_operand offset initial = SOME (n2w off) /\ eval_operand child_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ abi_decoder_operand_live st.cs_next_var child_len /\
  h < dimword (:256) /\ p < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?ready. abi_encoder_member_phase_raw st final initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_child_suffix_sequence >> strip_tac >>
  qexists_tac `actual with vs_inst_idx := LENGTH final.cs_current_insts` >>
  simp[abi_encoder_member_phase_raw_def] >> qexists_tac `actual` >> simp[]
QED

Theorem abi_encoder_member_cursor_transport:
  abi_encode_child_suffix head dyn_ptr offset child_len st = (out,final) /\
  eval_operand head initial = SOME (n2w h) /\ eval_operand dyn_ptr initial = SOME (n2w p) /\
  eval_operand offset initial = SOME (n2w off) /\ eval_operand child_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var dyn_ptr /\ abi_decoder_operand_live st.cs_next_var child_len /\
  h < dimword (:256) /\ p < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  eval_operand out ready = SOME (n2w len) /\ fresh_vars_wrt limit_st ready /\
  ready.vs_memory = (mstore p (n2w (off+len)) (mstore h (n2w off) initial)).vs_memory /\
  abi_decode_footprint_frame [(h,32);(p,32)] initial ready /\
  ready.vs_allocas = initial.vs_allocas /\ ready.vs_alloca_next = initial.vs_alloca_next /\
  ready.vs_halted = initial.vs_halted /\
  (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
    eval_operand op ready = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_child_suffix_sequence >> strip_tac >>
  gvs[abi_encoder_member_phase_raw_def] >>
  gvs[eval_op_inst_idx, fresh_vars_wrt_def, abi_decode_footprint_frame_def]
QED

Theorem abi_encoder_member_tail_raw:
  abi_encode_array_tail data_op dyn_ptr st = (ops,final) /\
  eval_operand data_op initial = SOME (n2w d) /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data_op /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?ready. abi_encoder_member_phase_raw st final initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_tail_sequence >> strip_tac >>
  gvs[abi_builtin_prefix_def] >>
  qexists_tac `actual with vs_inst_idx := LENGTH final.cs_current_insts` >>
  simp[abi_encoder_member_phase_raw_def] >> qexists_tac `actual` >> simp[]
QED

Theorem abi_encoder_member_tail_transport:
  abi_encode_array_tail data_op dyn_ptr st = (ops,final) /\
  eval_operand data_op initial = SOME (n2w d) /\ eval_operand dyn_ptr initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data_op /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  eval_operand (FST ops) ready = SOME (n2w off) /\
  eval_operand (SND ops) ready = SOME (n2w (d+off)) /\
  fresh_vars_wrt limit_st ready /\ abi_decoder_address_frame st.cs_next_var initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_array_tail_sequence >> strip_tac >>
  gvs[abi_builtin_prefix_def, abi_encoder_member_phase_raw_def] >>
  gvs[eval_op_inst_idx, fresh_vars_wrt_def, abi_decoder_address_frame_def]
QED

Theorem abi_encoder_member_phase_extend_sim:
  final.cs_blocks = st.cs_blocks /\ final.cs_current_bb = st.cs_current_bb /\ inst_extends st final /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st final) /\
  fn_has_code st final func /\ abi_encoder_member_phase_raw st final initial ready /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_extend_sim ctx func initial ready
Proof
  strip_tac >> gvs[abi_encoder_member_phase_raw_def] >>
  irule abi_encoder_run_sequence_extend_sim >> simp[] >> qexists_tac `st` >> simp[]
QED

Theorem abi_encoder_member_binary_raw_sim:
  emit_op opc [lhs;rhs] st = (out,final) /\ (opc = ADD \/ opc = MUL) /\
  fn_has_code st final func /\ abi_encoder_member_phase_raw st final initial ready /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_decode_sim ctx func initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_emit_address_shape >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st final)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[mk_inst_def] >> Cases_on `opc = ADD` >> gvs[is_terminator_def]) >>
  drule_all abi_encoder_member_phase_extend_sim >>
  disch_then (qspec_then `ctx` mp_tac) >>
  simp[abi_encoder_extend_sim_sim]
QED

(* Enforce the early instruction layer's import boundary at build time. *)

Theorem abi_encoder_member_prefix_raw:
  abi_encode_child_prefix dst ho dp st = (ops,final) /\
  eval_operand dst initial = SOME (n2w d) /\ eval_operand dp initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dp /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?ready. abi_encoder_member_phase_raw st final initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_child_prefix_sequence >> strip_tac >>
  gvs[abi_builtin_prefix_def] >>
  qexists_tac `actual with vs_inst_idx := LENGTH final.cs_current_insts` >>
  simp[abi_encoder_member_phase_raw_def] >> qexists_tac `actual` >> simp[]
QED

Theorem abi_encoder_member_prefix_transport:
  abi_encode_child_prefix dst ho dp st = (ops,final) /\
  eval_operand dst initial = SOME (n2w d) /\ eval_operand dp initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dp /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  eval_operand (FST ops) ready = SOME (n2w (d+ho)) /\
  eval_operand (FST (SND ops)) ready = SOME (n2w off) /\
  eval_operand (SND (SND ops)) ready = SOME (n2w (d+off)) /\
  fresh_vars_wrt limit_st ready /\ abi_decoder_address_frame st.cs_next_var initial ready
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_child_prefix_sequence >> strip_tac >>
  gvs[abi_builtin_prefix_def, abi_encoder_member_phase_raw_def] >>
  gvs[eval_op_inst_idx, fresh_vars_wrt_def, abi_decoder_address_frame_def]
QED

Theorem abi_encoder_member_prefix_control:
  abi_encode_child_prefix dst ho dp st = (ops,final) /\
  eval_operand dst initial = SOME (n2w d) /\ eval_operand dp initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dp /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  ready.vs_current_bb = initial.vs_current_bb /\
  ready.vs_inst_idx = LENGTH final.cs_current_insts /\
  ready.vs_halted = initial.vs_halted
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_child_prefix_sequence >> strip_tac >>
  gvs[abi_builtin_prefix_def, abi_encoder_member_phase_raw_def] >>
  gvs[abi_decoder_address_frame_def] >>
  drule abi_encode_child_prefix_shape >> strip_tac >>
  irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_current_bb` run_inst_seq_preserves_field)) >>
  qexists_tac `emitted_insts st final` >> asm_rewrite_tac [] >>
  rpt strip_tac >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
  drule_all step_preserves_control_flow >> simp[]
QED

(* The cursor writes only the head word and its registered cursor slot. *)
Theorem abi_encoder_member_cursor_bytes:
  abi_encode_child_suffix head dp offset len st = (out,final) /\
  eval_operand head initial = SOME (n2w h) /\ eval_operand dp initial = SOME (n2w slot) /\
  eval_operand offset initial = SOME (n2w off) /\ eval_operand len initial = SOME (n2w n) /\
  abi_decoder_operand_live st.cs_next_var dp /\ abi_decoder_operand_live st.cs_next_var len /\
  h < dimword (:256) /\ slot < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready /\
  (q+cnt <= h \/ h+32 <= q) /\ (q+cnt <= slot \/ slot+32 <= q) ==>
  mem_bytes_at q cnt ready.vs_memory = mem_bytes_at q cnt initial.vs_memory /\
  eval_operand out ready = SOME (n2w n)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_member_cursor_transport >> strip_tac >>
  asm_rewrite_tac [] >> irule abi_encoder_child_suffix_preserves_tail >> simp[]
QED
