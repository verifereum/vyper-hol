(* Fixed cursor allocation/initialization observations; execution stays in
   abiEncoderComplexPrefix and abiScratchOwnedPrefix. *)
Theory abiEncoderSharedArrayInit
Ancestors
  abiEncoderComplexPrefix abiEncoderComplexCode abiEncoderMemberPhaseRaw
  abiEncoderPrimitiveEffect abiEncoderRegisteredEffect abiEncoderExtendSim
  abiDecoderAllocation abiDecoderContract abiDecoderReentry
  abiEncoderSharedContract abiEncoderOpenInputFrame abiScratchOwnedPrefix abiScratchPrefix
  abiScratchFootprint abiScratchEffect abiDecoderFrame abiDecoderFootprint
  context exprLoweringProps compileEnv emitHelper emitHelperProps venomInst venomState
  venomExecSemantics venomMemDefs instIdxIndep valueEncoding words list rich_list finite_map arithmetic

Theorem abi_encoder_cursor_update_inv[local]:
  alloca_inv (update_var x w s) = alloca_inv s
Proof
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def, update_var_def]
QED

Theorem abi_encoder_cursor_alloca_observations:
  exec_alloca inst s (32w:bytes32) = OK t ==>
  (t.vs_accounts,t.vs_transient,t.vs_logs,t.vs_requests) =
    (s.vs_accounts,s.vs_transient,s.vs_logs,s.vs_requests) /\
  (alloca_inv s ==> alloca_inv t)
Proof
  simp[exec_alloca_def, AllCaseEqs(), dimword_def] >> strip_tac >> gvs[] >>
  pure_rewrite_tac [abi_encoder_cursor_update_inv] >>
  simp[update_var_def] >> strip_tac >>
  irule abi_encoder_register_alloca_inv >> simp[]
QED

Theorem abi_encoder_complex_prefix_raw_observations:
  abi_encode_complex_prefix infos st = (dp,final) /\
  abi_encoder_member_phase_raw st final initial ready ==>
  ready.vs_accounts = initial.vs_accounts /\ ready.vs_transient = initial.vs_transient /\
  ready.vs_logs = initial.vs_logs /\ ready.vs_requests = initial.vs_requests /\
  (alloca_inv initial ==> alloca_inv ready)
Proof
  simp[abi_encode_complex_prefix_def, compile_alloc_buffer_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  gvs[abi_encoder_member_phase_raw_def, emitted_insts_def] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  gvs[DROP_LENGTH_APPEND, run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
    exec_read1_def, eval_operand_def, AllCaseEqs()] >>
  drule abi_encoder_cursor_alloca_observations >> strip_tac >>
  gvs[Once step_inst_base_def, exec_write2_def, eval_operand_def, AllCaseEqs()] >>
  fs[mstore_def, write_memory_with_expansion_def, alloca_inv_def,
    allocas_non_overlapping_def, alloca_next_valid_def] >> first_assum ACCEPT_TAC
QED

Theorem abi_encoder_complex_prefix_raw_transport:
  abi_encode_complex_prefix infos st = (dp,final) /\
  abi_decoder_budget first last b cap initial /\ st.cs_next_id IN abi_decoder_ids first last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready ==>
  abi_encoder_complex_prefix_post infos dp st.cs_next_var st.cs_next_id
    limit_st first last b cap initial ready
Proof
  strip_tac >> drule_all abi_encoder_complex_prefix_sequence >>
  disch_then (qx_choose_then `raw` (qx_choose_then `slot` strip_assume_tac)) >>
  gvs[abi_encoder_member_phase_raw_def] >>
  simp_tac bool_ss [abi_encoder_complex_prefix_post_inst_idx, abi_encoder_complex_prefix_post_def] >>
  qexists_tac `slot` >> simp[]
QED

Theorem abi_encoder_complex_prefix_raw_allocated:
  abi_encode_complex_prefix infos st = (dp,final) /\
  abi_encoder_member_phase_raw st final initial ready ==>
  !i r. FLOOKUP initial.vs_allocas i = SOME r ==> FLOOKUP ready.vs_allocas i = SOME r
Proof
  simp[abi_encode_complex_prefix_def, compile_alloc_buffer_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  gvs[abi_encoder_member_phase_raw_def, emitted_insts_def] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  gvs[DROP_LENGTH_APPEND, run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
    exec_read1_def, eval_operand_def, AllCaseEqs()] >>
  gvs[Once step_inst_base_def, exec_write2_def, eval_operand_def, AllCaseEqs()] >>
  gvs[exec_alloca_def, AllCaseEqs(), update_var_def, mstore_def,
    write_memory_with_expansion_def] >>
  rpt strip_tac >> gvs[FLOOKUP_UPDATE] >> Cases_on `st.cs_next_id = i` >> gvs[]
QED

Theorem abi_encoder_complex_prefix_raw_registered:
  abi_encode_complex_prefix (infos:(abi_enc_info # num # num # bool) list) st = (dp,final) /\
  abi_decoder_budget first last b cap initial /\ st.cs_next_id IN abi_decoder_ids first last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_encoder_member_phase_raw st final initial ready /\ st.cs_next_id IN ids ==>
  abi_encoder_registered_effect ids outs initial ready /\ (alloca_inv initial ==> alloca_inv ready)
Proof
  strip_tac >>
  `abi_encoder_complex_prefix_post infos dp st.cs_next_var st.cs_next_id
    limit_st first last b cap initial ready` by
    (irule abi_encoder_complex_prefix_raw_transport >> asm_rewrite_tac [] >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all abi_encoder_complex_prefix_raw_observations >> strip_tac >>
  drule abi_encoder_complex_prefix_raw_allocated >> disch_then drule >> disch_tac >>
  qpat_assum `abi_encoder_complex_prefix_post _ _ _ _ _ _ _ _ _ _ _`
    (qx_choose_then `slot` strip_assume_tac o PURE_REWRITE_RULE [abi_encoder_complex_prefix_post_def]) >>
  simp_tac bool_ss [abi_encoder_registered_effect_def] >> asm_rewrite_tac [] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  rpt strip_tac >>
  `a < slot \/ slot+32 <= a` by
    (first_x_assum (qspec_then `st.cs_next_id` mp_tac) >> simp[]) >>
  fs[abi_decode_frame_def] >> first_x_assum irule >> decide_tac
QED

Theorem abi_encoder_complex_prefix_raw_extend:
  abi_encode_complex_prefix infos st = (dp,final) /\ fn_has_code st final func /\
  abi_encoder_member_phase_raw st final initial ready /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_extend_sim ctx func initial ready
Proof
  strip_tac >> drule abi_encoder_complex_prefix_shape >> strip_tac >>
  drule_all abi_encoder_member_phase_extend_sim >> simp[]
QED
