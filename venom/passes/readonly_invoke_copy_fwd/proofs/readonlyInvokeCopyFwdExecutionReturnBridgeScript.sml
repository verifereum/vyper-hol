Theory readonlyInvokeCopyFwdExecutionReturnBridge
Ancestors
  readonlyInvokeCopyFwdExecutionBoundary readonlyInvokeCopyFwdExecutionReturn
  readonlyInvokeCopyFwdHeterogeneousLifecycle
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdHistoryPhase readonlyInvokeCopyFwdRel
  readonlyInvokeCopyFwdMapCoverage readonlyInvokeCopyFwdAnalyzedOrigins
  readonlyInvokeCopyFwdExecutionHistory
  readonlyInvokeCopyFwdExecutionHistoryLifecycle readonlyInvokeCopyFwdExecutionRetirement
  readonlyInvokeCopyFwdLiveCertificates
  readonlyInvokeCopyFwdAnalyzedLifecycle
  o1LowerDloadOccurrence o1LowerDloadPtrDiscipline o1LowerDloadGhost
  reachableFnSim passSharedProps opcodeClass ptrDiscipline o1PassContract unitShapeDefs
  ctxLookupAgreeHelpers allocaFrontierBound
  stateEquiv stateEquivProps stateFrame
  venomExecSemantics venomInstProofs1 venomState venomInst
  finite_map list pred_set

Theorem ricf_execution_ret_result:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets tn /\
  ricf_mapped_support a B E PG G sites /\
  ricf_analyzed_origins vs C stk PG G tn fn inst s a U B history sites maps /\
  ricf_history_certificates vs C log_of stk PG G tn fn inst s a U B
    history certificates /\ ricf_chosen_support vs C log_of a fn B E /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  active_inst fn inst s /\ active_inst (mid_of fn) inst t /\
  inst.inst_opcode = RET /\ step_inst fuel C inst s = IntRet ret se ==>
  step_inst fuel Ct inst t = IntRet ret t /\
  ricf_execution_return vs C Ct mid_of log_of D a U
    (DRESTRICT B {id | FST id <> a}) {id | id IN E /\ FST id <> a}
    (FILTER (\entry. SND entry <> []) history)
    (FILTER (\entry. SND entry <> []) certificates) sites maps targets
    stk PG G tn fn ret se t
Proof
  strip_tac >> drule_all ricf_execution_ret_boundary >>
  disch_then (qspec_then `Ct` strip_assume_tac) >> simp[] >>
  simp[ricf_execution_return_def] >>
  qexistsl_tac [`inst`,`s`,`t`,`t`,`fuel`,`fuel`,`n`,`B`,`HP`,`H`,
                `history`,`certificates`,`E`] >>
  simp[execution_equiv_refl]
QED

Theorem ricf_execution_block_clear_nops:
  bb_well_formed tb /\
  block_step_rel D vs C
    (ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
    (ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
    stk PG fn r (run_block m Ct tb t) ==>
  block_step_rel D vs C
    (ricf_execution_boundary vs C mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
    (ricf_execution_return vs C Ct mid_of log_of D a U B0 E0 outer_history outer_certificates sites maps targets)
    stk PG fn r (run_block m Ct (clear_nops_block tb) t)
Proof
  strip_tac >> drule clear_nops_run_block_equiv >>
  disch_then (qspecl_then [`m`,`Ct`,`t`] mp_tac) >>
  Cases_on `run_block m Ct tb t` >>
  Cases_on `run_block m Ct (clear_nops_block tb) t` >> Cases_on `r` >>
  gvs[result_equiv_def, block_step_rel_def, fn_run_rel_def]
  >- metis_tac[state_equiv_empty_eq]
  >- (fs[dead_result_rel_def, execution_equiv_def,
         execution_frame_eq_reconstruct] >>
      strip_tac >> gvs[venom_state_component_equality])
  >- (strip_tac >> gvs[dead_result_rel_def]) >>
  rpt strip_tac >>
  metis_tac[ricf_execution_return_transport, run_block_IntRet_control]
QED

(* The observed callee exit may have its NOPs removed.  Restore the actual
   caller from that exact exit; only the callee's ignored index is erased. *)
Theorem ricf_execution_return_resume:
  ricf_execution_return vs C Ct mid_of log_of D a (u::U) B0 E0 outer_history outer_certificates current
    (sites::maps) (caller::targets) (f::stk) PG G tn fn ret se te /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
  active_inst f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ?t' n history certificates.
    bind_outputs f.cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state caller te)) = SOME t' /\
    FILTER (\entry. SND entry <> []) history = outer_history /\
    FILTER (\entry. SND entry <> []) certificates = outer_certificates /\
    ricf_analyzed_origins vs C stk f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      u.of_owner U B0 (ricf_phase_pop history) sites maps /\
    ricf_history_certificates vs C log_of stk f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      u.of_owner U B0 (ricf_phase_pop history)
      (ricf_live_ledger (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
        (ricf_phase_pop certificates)) /\
    ricf_execution_invariant vs C D stk f.cf_params
      (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
      f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      (t' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      n u.of_owner U B0 u.of_params
      (DRESTRICT u.of_prov (COMPL (set f.cf_inst.inst_outputs)))
      (ricf_live_ledger (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
        (ricf_phase_pop certificates)) E0 sites maps targets
      (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
Proof
  simp[ricf_execution_return_def] >> strip_tac >>
  `frame_reachable vs C (f::stk) PG G tn fn inst sr` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    metis_tac[ptr_discipline_fn_ptr_ok] >>
  `MEM fn C.ctx_functions` by metis_tac[frame_reachable_prov_support] >>
  `MEM inst (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
  `inst.inst_opcode <> RETFMP /\ inst.inst_opcode <> DRET` by
    (fs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
  `inst.inst_opcode <> INVOKE` by
    (strip_tac >>
     qpat_x_assum `step_inst sfuel C inst sr = _` mp_tac >>
     simp[Once step_inst_def, AllCaseEqs(), bind_outputs_def]) >>
  `inst.inst_opcode = RET` by
    (qpat_x_assum `step_inst sfuel C inst sr = _` mp_tac >>
     simp[step_inst_non_invoke] >> strip_tac >>
     drule step_inst_base_intret_opcodes >> simp[]) >>
  drule_all ricf_execution_ret_boundary >>
  disch_then (qspec_then `Ct` strip_assume_tac) >>
  `rawte = tr` by
    (qpat_x_assum `step_inst tfuel Ct inst tr = _` mp_tac >>
     qpat_x_assum `step_inst sfuel Ct inst tr = _` mp_tac >>
     simp[step_inst_non_invoke]) >>
  `execution_equiv {} tr te` by metis_tac[] >>
  `occ_frame_reachable vs C (f::stk) PG G tn fn inst sr
    n a (u::U) B HP H` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  drule_all ricf_analyzed_origins_return >> strip_tac >>
  `s'.vs_current_bb =
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)).vs_current_bb` by
    (irule bind_outputs_preserves >> simp[update_var_def] >> metis_tac[]) >>
  `s'.vs_current_bb = f.cf_state.vs_current_bb` by
    gvs[adopt_return_fmp_def, merge_callee_state_def] >>
  drule_all ricf_history_certificates_return >> strip_tac >>
  drule_all ricf_execution_ret_restore >>
  disch_then (qspec_then `Ct` strip_assume_tac) >>
  `set (ricf_live_ledger (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
      (ricf_phase_pop certificates)) SUBSET set (ricf_phase_pop certificates)` by
    simp[ricf_live_ledger_subset] >>
  drule_all ricf_execution_certificates_subset >> strip_tac >>
  qexistsl_tac [`t'`,`n`,`history`,`certificates`] >> simp[] >> gvs[]
QED
