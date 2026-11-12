Theory abiDecodePtrRejectSequence
Ancestors
  abiDecodePtrReentryStep abiDecodePtrReentryObservations
  abiDecodePtrAbortReentry abiDecoderVarSequence abiDecoderVarExtend
  abiDecodePtrRejectChecks abiDecodePtrNormalizedCompose
  abiEncoderVarTransport fragGasSeqPtr ptrSafeRun ptrDiscipline
  exprLoweringProps fragExec instIdxIndep execEquivParamDefs venomExecSemantics
  venomState venomInst list

Theorem abi_decode_ptr_abort_reentry:
  abi_decoder_vars_extend extras r r' /\
  abi_decoder_reentry_opcode bad.inst_opcode /\
  abi_decoder_inputs_defined bad r /\
  step_inst_base bad r = Abort Revert_abort u /\
  ptr_inst_ok D lo fuel ctx fn H tm bad r ==>
  ptr_inst_ok D lo fuel ctx fn H tm bad r'
Proof
  strip_tac >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) [] /\
   run_inst_seq [] r = OK r` by simp[run_inst_seq_def] >>
  drule_all abi_decode_rejecting_prefix_reentry >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  gvs[run_inst_seq_def] >>
  drule_all abi_decode_ptr_reentry_access >> strip_tac >>
  drule_all abi_decode_ptr_reentry_taint_ok >> strip_tac >>
  drule_all abi_decoder_reentry_non_invoke >> strip_tac >>
  `r.vs_allocas = r'.vs_allocas /\ r.vs_initial_fmp = r'.vs_initial_fmp /\
   r.vs_fmp = r'.vs_fmp` by
    (drule abi_decoder_vars_extend_restore >>
     disch_then (mp_tac o AP_TERM ``\z:venom_state.
       (z.vs_allocas,z.vs_initial_fmp,z.vs_fmp)``) >> simp[]) >>
  gvs[ptr_inst_ok_def, allocas_from_def, allocas_below_fmp_def,
    step_inst_non_invoke] >> metis_tac[]
QED

Theorem abi_decode_ptr_reject_prefix_replay[local]:
  !pre extras s t r u bad post G tn H tm.
  EVERY (\i. ~is_terminator i.inst_opcode) (pre ++ bad::post) /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) pre /\
  abi_decoder_reentry_opcode bad.inst_opcode /\
  abi_decoder_vars_extend extras s t /\ run_inst_seq pre s = OK r /\
  abi_decoder_inputs_defined bad r /\
  step_inst_base bad r = Abort Revert_abort u /\
  inst_seq_ptr D lo ctx fn PG G tn (pre ++ bad::post) s H tm ==>
  inst_seq_ptr D lo ctx fn PG G tn (pre ++ bad::post) t H tm
Proof
  Induct >- (simp[run_inst_seq_def, inst_seq_ptr_def] >>
    rpt strip_tac >>
    drule_all abi_decode_ptr_abort_reentry >> strip_tac >>
    `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) [] /\
     run_inst_seq [] s = OK s` by simp[run_inst_seq_def] >>
    drule_all abi_decode_rejecting_prefix_reentry >>
    disch_then (qspec_then `post` strip_assume_tac) >>
    gvs[run_inst_seq_def]) >>
  qx_gen_tac `inst` >> rpt gen_tac >>
  simp_tac bool_ss [APPEND, EVERY_DEF, run_inst_seq_def] >> strip_tac >>
  Cases_on `step_inst_base inst s` >> gvs[] >>
  rename1 `step_inst_base inst s = OK mid` >>
  drule_all abi_decoder_step_vars_extend >> strip_tac >>
  rename1 `step_inst_base inst t = OK actual` >>
  fs[inst_seq_ptr_def] >>
  `ptr_inst_ok D lo 0 ctx fn G tn inst t` by
    metis_tac[abi_decode_ptr_reentry_inst] >> simp[] >>
  `step_prov PG G inst mid = step_prov PG G inst actual` by
    metis_tac[abi_decode_ptr_reentry_prov] >>
  `step_taint inst s mid tn = step_taint inst t actual tn` by
    metis_tac[abi_decode_ptr_reentry_taint, abi_decoder_step_inputs_defined] >>
  `s.vs_inst_idx = t.vs_inst_idx` by
    metis_tac[abi_decode_ptr_reentry_frame] >>
  `run_inst_seq pre (mid with vs_inst_idx := SUC s.vs_inst_idx) =
    OK (r with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  `abi_decoder_vars_extend extras
    (mid with vs_inst_idx := SUC s.vs_inst_idx)
    (actual with vs_inst_idx := SUC t.vs_inst_idx)` by
    metis_tac[abi_encoder_vars_extend_idx] >>
  `abi_decoder_inputs_defined bad (r with vs_inst_idx := SUC s.vs_inst_idx)` by
    fs[abi_decoder_inputs_defined_def, lookup_var_def] >>
  `step_inst_base bad (r with vs_inst_idx := SUC s.vs_inst_idx) =
    Abort Revert_abort (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[step_inst_inst_idx_indep, exec_result_map_def] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

(* Replay only the executed prefix; no restriction on unreachable inputs. *)
Theorem abi_decode_ptr_reject_sequence_extend:
  EVERY (\i. ~is_terminator i.inst_opcode) code /\
  abi_decoder_vars_extend extras s t /\
  abi_decode_reject_witness code s u /\
  inst_seq_ptr D lo ctx fn PG G tn code s H tm ==>
  ?v. run_inst_seq code t = Abort Revert_abort v /\
      vsr_term_frame u = vsr_term_frame v /\
      inst_seq_ptr D lo ctx fn PG G tn code t H tm
Proof
  simp_tac bool_ss [abi_decode_reject_witness_def] >> strip_tac >>
  qpat_x_assum `code = _` SUBST_ALL_TAC >>
  `inst_seq_ptr D lo ctx fn PG G tn (pre ++ bad::post) t H tm` by
    (irule abi_decode_ptr_reject_prefix_replay >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  drule_all abi_decode_rejecting_prefix_reentry >>
  disch_then (qspec_then `post` strip_assume_tac) >>
  goal_assum (drule_at Any) >> gvs[]
QED
