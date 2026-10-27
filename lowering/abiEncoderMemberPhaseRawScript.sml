(* Early concrete member endpoints: no legacy member invariant owners. *)
Theory abiEncoderMemberPhaseRaw
Ancestors
  abiEncoderChildSuffix abiDecoderFrame
  abiDecoderReentryAddress abiDecoderReentry abiDecoderDynamicLoopSetup
  abiDecoderContract abiDecoderLoop fragExec compileEnv venomState
  venomExecSemantics instIdxIndep words list

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
