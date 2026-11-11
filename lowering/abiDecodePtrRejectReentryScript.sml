Theory abiDecodePtrRejectReentry
Ancestors
  abiDecodePtrReentryStep abiDecodePtrReentryObservations abiDecodePtrReentry
  abiDecodePtrAbortReentry abiDecoderVarSequence abiDecoderVarExtend
  abiEncoderVarTransport fragGasSeqPtr bodyPtrBopScalarSeq
  ptrSafeRun ptrDiscipline fragExec instIdxIndep execEquivParamDefs
  venomExecSemantics venomState venomInst list exprLoweringProps

Theorem abi_decode_ptr_assert_reentry:
  abi_decoder_vars_extend extras r r' /\ bad.inst_opcode = ASSERT /\
  abi_decoder_inputs_defined bad r /\
  step_inst_base bad r = Abort Revert_abort u /\
  ptr_inst_ok D lo fuel ctx fn H tm bad r ==>
  ptr_inst_ok D lo fuel ctx fn H tm bad r'
Proof
  strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) [] /\
   abi_decoder_reentry_opcode bad.inst_opcode /\ run_inst_seq [] r = OK r` by
    simp[abi_decoder_reentry_opcode_def, run_inst_seq_def] >>
  drule_all abi_decode_rejecting_prefix_reentry >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  gvs[run_inst_seq_def] >>
  drule_all abi_decode_ptr_reentry_access >> strip_tac >>
  drule_all abi_decode_ptr_reentry_taint_ok >> strip_tac >>
  `r.vs_allocas = r'.vs_allocas /\ r.vs_initial_fmp = r'.vs_initial_fmp /\
   r.vs_fmp = r'.vs_fmp` by
    (drule abi_decoder_vars_extend_restore >>
     disch_then (mp_tac o AP_TERM ``\z:venom_state.
       (z.vs_allocas,z.vs_initial_fmp,z.vs_fmp)``) >> simp[]) >>
  gvs[ptr_inst_ok_def, allocas_from_def, allocas_below_fmp_def,
    step_inst_non_invoke] >> metis_tac[]
QED

Theorem abi_decode_ptr_rejecting_prefix_extend:
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
    ~is_terminator i.inst_opcode) pre /\
  abi_decoder_vars_extend extras s t /\ run_inst_seq pre s = OK r /\
  inst_seq_ptr D lo ctx fn PG G tn pre s H tm /\
  bad.inst_opcode = ASSERT /\ abi_decoder_inputs_defined bad r /\
  step_inst_base bad r = Abort Revert_abort u /\
  ptr_inst_ok D lo 0 ctx fn H tm bad
    (r with vs_inst_idx := s.vs_inst_idx + LENGTH pre) ==>
  ?r' u'. run_inst_seq pre t = OK r' /\
    abi_decoder_vars_extend extras r r' /\
    step_inst_base bad r' = Abort Revert_abort u' /\
    vsr_term_frame u = vsr_term_frame u' /\
    run_inst_seq (pre ++ bad::post) t = Abort Revert_abort u' /\
    inst_seq_ptr D lo ctx fn PG G tn (pre ++ bad::post) t H tm
Proof
  strip_tac >>
  drule_all abi_decode_ptr_sequence_extend >> strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) pre /\
   abi_decoder_reentry_opcode bad.inst_opcode` by
    fs[EVERY_CONJ, abi_decoder_reentry_opcode_def] >>
  drule_all abi_decode_rejecting_prefix_reentry >>
  disch_then (qspec_then `post` strip_assume_tac) >>
  `s.vs_inst_idx = t.vs_inst_idx` by metis_tac[abi_decode_ptr_reentry_frame] >>
  `abi_decoder_vars_extend extras
     (r with vs_inst_idx := s.vs_inst_idx + LENGTH pre)
     (r' with vs_inst_idx := t.vs_inst_idx + LENGTH pre)` by
    metis_tac[abi_encoder_vars_extend_idx] >>
  `abi_decoder_inputs_defined bad
     (r with vs_inst_idx := s.vs_inst_idx + LENGTH pre)` by
    fs[abi_decoder_inputs_defined_def, lookup_var_def] >>
  `step_inst_base bad (r with vs_inst_idx := s.vs_inst_idx + LENGTH pre) =
     Abort Revert_abort (u with vs_inst_idx := s.vs_inst_idx + LENGTH pre)` by
    simp[step_inst_inst_idx_indep, exec_result_map_def, is_terminator_def] >>
  drule_all abi_decode_ptr_assert_reentry >> strip_tac >>
  `step_inst_base bad (r' with vs_inst_idx := t.vs_inst_idx + LENGTH pre) =
     Abort Revert_abort (u' with vs_inst_idx := t.vs_inst_idx + LENGTH pre)` by
    simp[step_inst_inst_idx_indep, exec_result_map_def, is_terminator_def] >>
  `inst_seq_ptr D lo ctx fn PG H tm (bad::post)
     (r' with vs_inst_idx := t.vs_inst_idx + LENGTH pre) H tm` by
    simp[inst_seq_ptr_def] >>
  `inst_seq_ptr D lo ctx fn PG G tn (pre ++ bad::post) t H tm` by
    (`EVERY (\i. ~is_terminator i.inst_opcode) pre` by fs[EVERY_CONJ] >>
     drule_all bop_inst_seq_ptr_append >> simp[]) >>
  goal_assum (drule_at Any) >> gvs[]
QED
