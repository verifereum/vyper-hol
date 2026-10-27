(* Early concrete member endpoints: no legacy member invariant owners. *)
Theory abiEncoderMemberPhaseRaw
Ancestors
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
