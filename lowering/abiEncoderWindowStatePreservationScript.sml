(* Actual-execution frame and dynamic-allocation room transport. *)
Theory abiEncoderWindowStatePreservation
Ancestors
  entryDecoderStateFrame abiDecoderVarSequence intCallCallee
  exprLoweringProps venomExecSemantics venomState venomInst list

Theorem encoder_step_observations[local]:
  (abi_decoder_reentry_opcode inst.inst_opcode \/
   MEM inst.inst_opcode [SUB;Div;Mod;AND;OR;XOR;NOT;SAR;ASSIGN;NOP]) /\
  step_inst_base inst s = OK t ==> entry_decoder_obs s t
Proof
  strip_tac
  >- metis_tac[entry_decoder_step_obs] >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
  pure_rewrite_tac[step_inst_base_def] >> asm_rewrite_tac[] >>
  pure_rewrite_tac[opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), entry_decoder_obs_def, update_var_def]
QED

Theorem encoder_sequence_observations:
  !code s t.
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode \/
    MEM i.inst_opcode [SUB;Div;Mod;AND;OR;XOR;NOT;SAR;ASSIGN;NOP]) code /\
  run_inst_seq code s = OK t ==> entry_decoder_obs s t
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  `entry_decoder_obs s v` by
    (irule encoder_step_observations >> goal_assum (drule_at Any) >> simp[]) >>
  first_x_assum drule_all >> metis_tac[entry_decoder_obs_trans]
QED

Theorem abi_encoder_sequence_static:
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode \/
    MEM i.inst_opcode [SUB;Div;Mod;AND;OR;XOR;NOT;SAR;ASSIGN;NOP]) code /\
  run_inst_seq code s = OK t ==>
  (t with vs_inst_idx := ix).vs_call_ctx = s.vs_call_ctx /\
  (t with vs_inst_idx := ix).vs_tx_ctx = s.vs_tx_ctx /\
  (t with vs_inst_idx := ix).vs_block_ctx = s.vs_block_ctx /\
  (t with vs_inst_idx := ix).vs_outcomes = s.vs_outcomes /\
  (t with vs_inst_idx := ix).vs_fmp = s.vs_fmp
Proof
  strip_tac >> drule_all encoder_sequence_observations >>
  simp[entry_decoder_obs_def]
QED

Theorem abi_encoder_sequence_room:
  run_inst_seq code s = OK t /\
  EVERY (\i. MEM i (fn_insts func) /\ i.inst_opcode <> INVOKE) code /\
  fmp_room ctx func s /\ t.vs_fmp = s.vs_fmp ==>
  fmp_room ctx func (t with vs_inst_idx := ix)
Proof
  strip_tac >> drule_all run_inst_seq_fmp_room >>
  simp[fmp_room_def, pending_alloca_size_def]
QED
