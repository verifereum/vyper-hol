(* Observations of the existing seven-instruction address execution. *)
Theory abiEncoderSharedArrayAddress
Ancestors
  abiEncoderArrayAddress abiEncoderMemberPhaseRaw abiEncoderSharedArrayHeader abiEncoderSequence
  abiEncoderRegisteredEffect abiEncoderExtendSim abiScratchAddress
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderContract valueEncoding
  abiEncoderArrayCode emitHelper exprLoweringProps compileEnv emitHelperProps
  venomState venomMemDefs venomExecSemantics venomInst instIdxIndep list rich_list words arithmetic

Theorem abi_encoder_array_address_opcodes[local]:
  abi_encode_array_addresses ip src dst asz msz st = (coords,final) ==>
  EVERY (\i. i.inst_opcode = ADD \/ i.inst_opcode = MUL \/ i.inst_opcode = MLOAD)
    (emitted_insts st final)
Proof
  simp[abi_encode_array_addresses_def, abi_decode_array_head_setup_def,
    abi_decode_indexed_coordinates_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encoder_array_address_step_globals[local]:
  (i.inst_opcode = ADD \/ i.inst_opcode = MUL \/ i.inst_opcode = MLOAD) /\
  step_inst_base i s = OK t ==>
  (t.vs_accounts,t.vs_transient,t.vs_logs,t.vs_requests) =
  (s.vs_accounts,s.vs_transient,s.vs_logs,s.vs_requests)
Proof
  strip_tac >>
  gvs[step_inst_base_def, exec_pure2_def, exec_read1_def,
    AllCaseEqs(), update_var_def]
QED

Theorem abi_encoder_array_address_raw_globals:
  abi_encode_array_addresses ip src dst asz msz st = (coords,final) /\
  abi_encoder_member_phase_raw st final initial actual ==>
  actual.vs_accounts = initial.vs_accounts /\ actual.vs_transient = initial.vs_transient /\
  actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests
Proof
  strip_tac >> drule abi_encoder_array_address_opcodes >> disch_tac >>
  gvs[abi_encoder_member_phase_raw_def] >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK raw` >>
  `(raw.vs_accounts,raw.vs_transient,raw.vs_logs,raw.vs_requests) =
   (initial.vs_accounts,initial.vs_transient,initial.vs_logs,initial.vs_requests)` by
    (irule (BETA_RULE (Q.ISPEC
       `\s:venom_state. (s.vs_accounts,s.vs_transient,s.vs_logs,s.vs_requests)`
       run_inst_seq_preserves_field)) >>
     qexists_tac `emitted_insts st final` >> asm_rewrite_tac [] >>
     rpt strip_tac >> irule abi_encoder_array_address_step_globals >>
     fs[EVERY_MEM] >> metis_tac[]) >> gvs[]
QED

Theorem abi_encoder_shared_array_address_reach:
  abi_encode_array_addresses ip src dst asz msz st = (coords,final) /\
  fn_has_code st final func /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_member_phase_raw st final initial actual /\
    eval_operand (FST (FST coords)) actual = SOME (n2w j) /\
    eval_operand (SND (FST coords)) actual = SOME (n2w (sb+32+j*msz)) /\
    eval_operand (FST (SND coords)) actual = SOME (n2w (d+32)) /\
    eval_operand (SND (SND coords)) actual = SOME (n2w (d+32+j*asz)) /\
    abi_decoder_operand_live final.cs_next_var (FST (FST coords)) /\
    abi_decoder_operand_live final.cs_next_var (SND (FST coords)) /\
    abi_decoder_operand_live final.cs_next_var (FST (SND coords)) /\
    abi_decoder_operand_live final.cs_next_var (SND (SND coords)) /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_address_frame st.cs_next_var initial actual /\
    abi_encoder_registered_effect ids outs initial actual /\
    (alloca_inv initial ==> alloca_inv actual) /\
    abi_encoder_extend_sim ctx func initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\ ~actual.vs_halted
Proof
  strip_tac >> drule abi_encode_array_addresses_shape >> strip_tac >>
  drule_all abi_encode_array_addresses_sequence >>
  disch_then (qx_choose_then `raw` strip_assume_tac) >>
  qabbrev_tac `actual = raw with vs_inst_idx := LENGTH final.cs_current_insts` >>
  `abi_encoder_member_phase_raw st final initial actual` by
    (simp[abi_encoder_member_phase_raw_def, Abbr `actual`] >>
     qexists_tac `raw` >> simp[]) >>
  `abi_decoder_address_frame st.cs_next_var initial actual /\ fresh_vars_wrt limit_st actual` by
    gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, Abbr `actual`, eval_op_inst_idx] >>
  `actual.vs_accounts = initial.vs_accounts /\ actual.vs_transient = initial.vs_transient /\
   actual.vs_logs = initial.vs_logs /\ actual.vs_requests = initial.vs_requests` by
    (drule_all abi_encoder_array_address_raw_globals >> simp[]) >>
  `abi_encoder_registered_effect ids outs initial actual /\
   (alloca_inv initial ==> alloca_inv actual)` by
    fs[abi_encoder_registered_effect_def, abi_decoder_address_frame_def,
       alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  `abi_encoder_extend_sim ctx func initial actual` by
    (irule abi_encoder_member_phase_extend_sim >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`final`,`st`] >> fs[EVERY_CONJ]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st final)` by fs[EVERY_CONJ] >>
  drule_all abi_encoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `actual` >>
  gvs[abi_decoder_address_frame_def, Abbr `actual`, eval_op_inst_idx]
QED
