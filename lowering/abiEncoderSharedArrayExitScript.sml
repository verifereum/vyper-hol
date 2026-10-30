(* Read-only generated exits at the common raw endpoint. *)
Theory abiEncoderSharedArrayExit
Ancestors
  abiEncoderArrayExit abiEncoderArrayScalarCode abiEncoderArrayCode
  abiEncoderMemberPhaseRaw abiEncoderMemberPhaseEffect abiEncoderRegisteredEffect
  abiEncoderExtendSim abiBuiltinPrefix abiScratchEffect abiScratchLeafEffect abiDecoderAllocation
  abiDecoderFrame abiEncoderSharedArrayHeader abiEncoderSharedContract abiEncoderArrayPrefix
  abiDecoderReentry abiDecoderContract abiDecoderDynamicLoopSetup venomMemDefs
  exprLoweringProps compileEnv emitHelper emitHelperProps venomState venomInst
  venomExecSemantics venomInstProps instIdxIndep words list rich_list arithmetic

Theorem abi_encoder_phase_current_bb[local]:
  abi_encoder_member_phase_raw st final initial ready /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st final) ==>
  ready.vs_current_bb = initial.vs_current_bb
Proof
  simp_tac bool_ss [abi_encoder_member_phase_raw_def] >> strip_tac >> gvs[] >>
  irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_current_bb` run_inst_seq_preserves_field)) >>
  qexists_tac `emitted_insts st final` >> asm_rewrite_tac [] >> rpt strip_tac >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `step_inst 0 ctx i ss1 = OK ss2` by simp[step_inst_non_invoke] >>
  drule_all step_preserves_control_flow >> simp[]
QED

Theorem abi_encoder_array_static_exit_raw_transport:
  abi_encode_array_static_exit src asz st = (out,final) /\
  eval_operand src initial = SOME (n2w sb) /\ mload sb initial = n2w cnt /\
  sb < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ abi_encoder_member_phase_raw st final initial ready ==>
  eval_operand out ready = SOME (n2w (32+cnt*asz)) /\
  fresh_vars_wrt limit_st ready /\ abi_decoder_address_frame st.cs_next_var initial ready /\
  ready.vs_current_bb = initial.vs_current_bb /\ ready.vs_inst_idx = LENGTH final.cs_current_insts /\
  ready.vs_halted = initial.vs_halted
Proof
  strip_tac >> drule (CONJUNCT1 abi_encode_array_exit_shape) >> strip_tac >>
  `ready.vs_current_bb = initial.vs_current_bb` by
    (drule_all abi_encoder_phase_current_bb >> simp[]) >>
  drule_all abi_encode_array_static_exit_sequence >> strip_tac >>
  gvs[abi_builtin_prefix_def, abi_encoder_member_phase_raw_def,
    abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx] >> metis_tac[]
QED

Theorem abi_encoder_array_dynamic_exit_raw_transport:
  abi_encode_array_dynamic_exit src dp st = (out,final) /\
  eval_operand src initial = SOME src_word /\ eval_operand dp initial = SOME (n2w slot) /\
  abi_decoder_operand_live st.cs_next_var dp /\ mload slot initial = n2w off /\
  slot < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ abi_encoder_member_phase_raw st final initial ready ==>
  eval_operand out ready = SOME (n2w (32+off)) /\
  fresh_vars_wrt limit_st ready /\ abi_decoder_address_frame st.cs_next_var initial ready /\
  ready.vs_current_bb = initial.vs_current_bb /\ ready.vs_inst_idx = LENGTH final.cs_current_insts /\
  ready.vs_halted = initial.vs_halted
Proof
  strip_tac >> drule (CONJUNCT2 abi_encode_array_exit_shape) >> strip_tac >>
  `ready.vs_current_bb = initial.vs_current_bb` by
    (drule_all abi_encoder_phase_current_bb >> simp[]) >>
  drule_all abi_encode_array_dynamic_exit_sequence >> strip_tac >>
  gvs[abi_builtin_prefix_def, abi_encoder_member_phase_raw_def,
    abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_op_inst_idx] >> metis_tac[]
QED

Theorem abi_encoder_array_exit_opcodes:
  (if active then abi_encode_array_dynamic_exit src dp st = (out,final)
   else abi_encode_array_static_exit src asz st = (out,final)) ==>
  EVERY (\i. i.inst_opcode = ADD \/ i.inst_opcode = MUL \/ i.inst_opcode = MLOAD)
    (emitted_insts st final)
Proof
  Cases_on `active` >>
  simp[abi_encode_array_dynamic_exit_def, abi_encode_array_static_exit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encoder_array_exit_extend:
  (if active then abi_encode_array_dynamic_exit src dp st = (out,final)
   else abi_encode_array_static_exit src asz st = (out,final)) /\
  fn_has_code st final func /\ abi_encoder_member_phase_raw st final initial ready /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_extend_sim ctx func initial ready
Proof
  strip_tac >>
  Cases_on `active` >> gvs[]
  >- (drule (CONJUNCT2 abi_encode_array_exit_shape) >> strip_tac >>
      drule_all abi_encoder_member_phase_extend_sim >> simp[]) >>
  drule (CONJUNCT1 abi_encode_array_exit_shape) >> strip_tac >>
  drule_all abi_encoder_member_phase_extend_sim >> simp[]
QED

Theorem abi_encoder_array_exit_readonly:
  (if active then abi_encode_array_dynamic_exit src dp st = (out,final)
   else abi_encode_array_static_exit src asz st = (out,final)) /\
  abi_encoder_member_phase_raw st final initial ready ==>
  ready.vs_memory = initial.vs_memory /\
  ready.vs_allocas = initial.vs_allocas /\ ready.vs_alloca_next = initial.vs_alloca_next /\
  ready.vs_accounts = initial.vs_accounts /\ ready.vs_transient = initial.vs_transient /\
  ready.vs_logs = initial.vs_logs /\ ready.vs_requests = initial.vs_requests
Proof
  strip_tac >> drule abi_encoder_array_exit_opcodes >> strip_tac >>
  gvs[abi_encoder_member_phase_raw_def] >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK u` >>
  ` (u.vs_memory,u.vs_allocas,u.vs_alloca_next,u.vs_accounts,u.vs_transient,u.vs_logs,u.vs_requests) =
    (initial.vs_memory,initial.vs_allocas,initial.vs_alloca_next,initial.vs_accounts,
      initial.vs_transient,initial.vs_logs,initial.vs_requests)` by
    (irule (BETA_RULE (Q.ISPEC
       `\s:venom_state. (s.vs_memory,s.vs_allocas,s.vs_alloca_next,s.vs_accounts,
         s.vs_transient,s.vs_logs,s.vs_requests)` run_inst_seq_preserves_field)) >>
     qexists_tac `emitted_insts st final` >> asm_rewrite_tac [] >> rpt strip_tac >>
     `i.inst_opcode = ADD \/ i.inst_opcode = MUL \/ i.inst_opcode = MLOAD` by
       (fs[EVERY_MEM] >> metis_tac[]) >>
     gvs[step_inst_base_def, exec_pure2_def, exec_read1_def, AllCaseEqs(), update_var_def]) >>
  gvs[]
QED

Theorem abi_encoder_array_exit_registered:
  (if active then abi_encode_array_dynamic_exit src dp st = (out,final)
   else abi_encode_array_static_exit src asz st = (out,final)) /\
  abi_encoder_member_phase_raw st final initial ready ==>
  abi_encoder_registered_effect ids outs initial ready /\
  (alloca_inv initial ==> alloca_inv ready)
Proof
  strip_tac >> drule_all abi_encoder_array_exit_readonly >> strip_tac >>
  simp[abi_encoder_registered_effect_def, alloca_inv_def,
    allocas_non_overlapping_def, alloca_next_valid_def]
QED

Theorem abi_encoder_array_exit_effect:
  (if active then abi_encode_array_dynamic_exit src dp st = (out,final)
   else abi_encode_array_static_exit src asz st = (out,final)) /\
  fn_has_code st final func /\ abi_encoder_member_phase_raw st final initial ready /\
  abi_decoder_address_frame st.cs_next_var initial ready /\ fresh_vars_wrt limit_st ready /\
  abi_decoder_budget first last b cap initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_scratch_effect first last lo hi st.cs_next_var limit_st d sz b cap initial ready /\
  abi_encoder_registered_effect (abi_decoder_ids lo hi) [(d,sz)] initial ready /\
  (alloca_inv initial ==> alloca_inv ready) /\ abi_encoder_extend_sim ctx func initial ready
Proof
  strip_tac >> drule_all abi_encoder_array_exit_readonly >> strip_tac >>
  drule_all abi_encoder_array_exit_registered >>
  disch_then (qspecl_then [`[(d,sz)]`,`abi_decoder_ids lo hi`] strip_assume_tac) >>
  drule_all abi_encoder_array_exit_extend >> disch_then (qspec_then `ctx` assume_tac) >>
  asm_simp_tac bool_ss [] >> irule abi_scratch_leaf_effect >>
  gvs[abi_decoder_address_frame_def, abi_decode_frame_def]
QED

Theorem abi_encoder_shared_array_exit_source:
  (if active then abi_encode_array_dynamic_exit src dp st = (out,final)
   else abi_encode_array_static_exit src asz st = (out,final)) /\
  abi_encoder_member_phase_raw st final initial ready /\
  abi_decoder_address_frame owner_st.cs_next_var initial ready /\
  abi_encoder_shared_input (ei,ty,av) (owner_st,source,dst)
    (sb,source_cap) (d,sz) (first,last,b,cap) initial /\
  abi_encoder_array_prefix elem_ty avs k d initial.vs_memory ==>
  abi_encoder_shared_input (ei,ty,av) (owner_st,source,dst)
    (sb,source_cap) (d,sz) (first,last,b,cap) ready /\
  abi_encoder_array_prefix elem_ty avs k d ready.vs_memory
Proof
  strip_tac >> drule_all abi_encoder_array_exit_readonly >> strip_tac >>
  drule_all abi_encoder_shared_input_address >> simp[]
QED
