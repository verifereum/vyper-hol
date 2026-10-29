(* Rich observations from actual primitive runs, not from weak simulation. *)
Theory abiEncoderMemberPhaseEffect
Ancestors
  abiEncoderMemberPhaseRaw abiEncoderPrimitiveEffect abiEncoderRegisteredEffect
  abiDecoderReentryAddress abiDecoderContract abiDecoderDynamicLoopSetup venomState venomExecSemantics
  compileEnv emitHelper emitHelperProps venomInst venomMemDefs exprLoweringProps
  abiEncoderChildCode abiEncoderChildSuffix words list rich_list

Theorem abi_encoder_member_binary_registered:
  emit_op opc [lhs;rhs] st = (out,final) /\ (opc = ADD \/ opc = MUL) /\
  eval_operand lhs initial = SOME a /\ eval_operand rhs initial = SOME b /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  abi_encoder_registered_effect ids outs initial ready /\
  (alloca_inv initial ==> alloca_inv ready)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_binary_reentry >> strip_tac >>
  gvs[abi_encoder_member_phase_raw_def] >>
  simp[abi_encoder_registered_effect_def, update_var_def,
    alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

Theorem abi_encoder_member_load_registered:
  emit_op MLOAD [src] st = (out,final) /\ eval_operand src initial = SOME p /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  abi_encoder_registered_effect ids outs initial ready /\
  (alloca_inv initial ==> alloca_inv ready)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`opc` |-> `MLOAD`, `s` |-> `initial:venom_state`,
    `st'` |-> `final:compile_state`] abi_decoder_read_reentry) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_decode_source_opcode_def] >> strip_tac >>
  gvs[abi_encoder_member_phase_raw_def] >>
  simp[abi_encoder_registered_effect_def, update_var_def,
    alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

Theorem abi_encoder_member_step_globals:
  (i.inst_opcode = ADD \/ i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) /\
  step_inst_base i s = OK t ==>
  (t.vs_accounts,t.vs_transient,t.vs_logs,t.vs_requests) =
  (s.vs_accounts,s.vs_transient,s.vs_logs,s.vs_requests)
Proof
  strip_tac >>
  gvs[step_inst_base_def, exec_pure2_def, exec_read1_def, exec_write2_def,
      AllCaseEqs(), update_var_def, mstore_def, write_memory_with_expansion_def]
QED

Theorem abi_encoder_member_phase_globals:
  EVERY (\i. i.inst_opcode = ADD \/ i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE)
    (emitted_insts st final) /\
  abi_encoder_member_phase_raw st final initial ready ==>
  ready.vs_accounts = initial.vs_accounts /\ ready.vs_transient = initial.vs_transient /\
  ready.vs_logs = initial.vs_logs /\ ready.vs_requests = initial.vs_requests
Proof
  strip_tac >> gvs[abi_encoder_member_phase_raw_def] >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK u` >>
  ` (u.vs_accounts,u.vs_transient,u.vs_logs,u.vs_requests) =
    (initial.vs_accounts,initial.vs_transient,initial.vs_logs,initial.vs_requests)` by
    (irule (BETA_RULE (Q.ISPEC
       `\s:venom_state. (s.vs_accounts,s.vs_transient,s.vs_logs,s.vs_requests)`
       run_inst_seq_preserves_field)) >>
     qexists_tac `emitted_insts st final` >> asm_rewrite_tac [] >>
     rpt strip_tac >> irule abi_encoder_member_step_globals >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  gvs[]
QED

Theorem abi_encoder_member_suffix_opcodes:
  abi_encode_child_suffix head dp offset len st = (out,final) ==>
  EVERY (\i. i.inst_opcode = ADD \/ i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE)
    (emitted_insts st final)
Proof
  simp[abi_encode_child_suffix_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encoder_member_cursor_registered:
  abi_encode_child_suffix head dp offset len st = (out,final) /\
  eval_operand head initial = SOME (n2w h) /\ eval_operand dp initial = SOME (n2w slot) /\
  eval_operand offset initial = SOME (n2w off) /\ eval_operand len initial = SOME (n2w n) /\
  abi_decoder_operand_live st.cs_next_var dp /\ abi_decoder_operand_live st.cs_next_var len /\
  h < dimword (:256) /\ slot < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready /\
  d <= h /\ h+32 <= d+cap /\ id IN ids /\
  FLOOKUP initial.vs_allocas id = SOME (slot,32) ==>
  abi_encoder_registered_effect ids [(d,cap)] initial ready /\
  (alloca_inv initial ==> alloca_inv ready)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_member_cursor_transport >> strip_tac >>
  `ready.vs_accounts = initial.vs_accounts /\ ready.vs_transient = initial.vs_transient /\
   ready.vs_logs = initial.vs_logs /\ ready.vs_requests = initial.vs_requests` by
    (irule abi_encoder_member_phase_globals >> goal_assum (drule_at Any) >>
     drule abi_encoder_member_suffix_opcodes >> simp[]) >>
  conj_tac
  >- (simp_tac bool_ss [abi_encoder_registered_effect_def] >> asm_rewrite_tac [] >>
      rpt strip_tac >>
      `a < slot \/ slot+32 <= a` by metis_tac[] >>
      `a < h \/ h+32 <= a` by (fs[] >> decide_tac) >>
      asm_rewrite_tac [] >>
      irule abi_encoder_child_suffix_preserves_tail >> decide_tac) >>
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

Theorem abi_encoder_member_prefix_opcodes:
  abi_encode_child_prefix dst ho dp st = (ops,final) ==>
  EVERY (\i. i.inst_opcode = ADD \/ i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE)
    (emitted_insts st final)
Proof
  simp[abi_encode_child_prefix_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encoder_member_prefix_registered:
  abi_encode_child_prefix dst ho dp st = (ops,final) /\
  eval_operand dst initial = SOME (n2w d) /\ eval_operand dp initial = SOME (n2w slot) /\
  mload slot initial = n2w off /\ slot < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dp /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  abi_encoder_registered_effect ids outs initial ready /\
  (alloca_inv initial ==> alloca_inv ready)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_member_prefix_transport >> strip_tac >>
  `ready.vs_accounts = initial.vs_accounts /\ ready.vs_transient = initial.vs_transient /\
   ready.vs_logs = initial.vs_logs /\ ready.vs_requests = initial.vs_requests` by
    (irule abi_encoder_member_phase_globals >> goal_assum (drule_at Any) >>
     drule abi_encoder_member_prefix_opcodes >> simp[]) >>
  gvs[abi_decoder_address_frame_def, abi_encoder_registered_effect_def,
    alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED
