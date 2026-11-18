Theory fmpStageFmpStepsRetBind
Ancestors
  fmpStageRel intCallStep o1LowerDloadRestore livenessProofs
  ptrDiscipline o1LowerDloadRelocationKernel
  contextCodegenRel venomExecProofs
  venomExecSemantics venomState venomInst finite_map list pred_set

(* The liveness premise says exactly which old values survive a return. *)
Theorem fmp_return_bind_env:
  fmp_env_rel sm fn live G tv s t /\
  ALL_DISTINCT outs /\
  (!v. MEM v next /\ ~MEM v outs ==> MEM v live) /\
  bind_outputs outs vals s = SOME s1 ==>
  ?t1. bind_outputs outs vals t = SOME t1 /\
    fmp_env_rel sm fn next (DRESTRICT G (COMPL (set outs)))
      (DRESTRICT tv (COMPL (set outs))) s1 t1
Proof
  strip_tac >>
  `LENGTH outs = LENGTH vals` by gvs[bind_outputs_def] >>
  `?t1. bind_outputs outs vals t = SOME t1` by simp[bind_outputs_def] >>
  qexists_tac `t1` >> simp[] >>
  imp_res_tac (cj 2 bind_outputs_lookup) >>
  imp_res_tac (cj 3 bind_outputs_lookup) >>
  simp[fmp_env_rel_def] >> rpt strip_tac >>
  Cases_on `MEM v outs`
  >- (`?n. n < LENGTH outs /\ v = EL n outs` by metis_tac[MEM_EL] >>
      gvs[] >>
      `lookup_var (EL n outs) s1 = SOME (EL n vals) /\
       lookup_var (EL n outs) t1 = SOME (EL n vals)` by metis_tac[] >>
      gvs[lookup_var_def, FLOOKUP_DRESTRICT, fmp_value_rel_def,
          op_taint_def, ld_value_agree_scalar, word_agree_except_def]) >>
  gvs[lookup_var_def] >>
  qpat_x_assum `fmp_env_rel _ _ _ _ _ _ _` mp_tac >>
  simp[fmp_env_rel_def] >> disch_then drule >> strip_tac >>
  qexists_tac `y` >> gvs[FLOOKUP_DRESTRICT, op_taint_def] >> metis_tac[]
QED

(* Only the caller's variable map changes when binding an ordinary return. *)
Theorem fmp_return_bind_caller:
  wf_function fn /\ active_inst fn inst s /\
  MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
  ALL_DISTINCT inst.inst_outputs /\
  fmp_env_rel sm fn
    (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
    G tv s t /\ fmp_params_rel sm PG s t /\
  ret.iret_adopt_fmp = NONE /\ ret'.iret_adopt_fmp = NONE /\
  ret'.iret_values = ret.iret_values /\ outs' = inst.inst_outputs /\
  bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s se)) = SOME s1 ==>
  ?t1.
    bind_outputs outs' ret'.iret_values
      (adopt_return_fmp ret' (merge_callee_state t te)) = SOME t1 /\
    fmp_env_rel sm fn
      (live_vars_at (liveness_analyze fn) s.vs_current_bb (SUC s.vs_inst_idx))
      (DRESTRICT G (COMPL (set inst.inst_outputs)))
      (DRESTRICT tv (COMPL (set inst.inst_outputs)))
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
    fmp_params_rel sm PG s1 t1 /\
    s1 = merge_callee_state s se with vs_vars := s1.vs_vars /\
    t1 = merge_callee_state t te with vs_vars := t1.vs_vars
Proof
  strip_tac >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb
               (SUC s.vs_inst_idx)) /\ ~MEM v inst.inst_outputs ==>
       MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)` by
    (gvs[active_inst_def] >> drule_all wf_lookup_block >> strip_tac >>
     rpt strip_tac >> drule live_vars_at_propagate >>
     simp[inst_defs_def] >> metis_tac[]) >>
  `fmp_env_rel sm fn
     (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
     G tv (merge_callee_state s se) (merge_callee_state t te)` by
    gvs[fmp_env_rel_def, merge_callee_state_def] >>
  gvs[adopt_return_fmp_def] >>
  drule_all fmp_return_bind_env >> strip_tac >>
  qexists_tac `t1` >> simp[] >>
  imp_res_tac (cj 4 bind_outputs_lookup) >>
  gvs[fmp_env_rel_def, fmp_params_rel_def, merge_callee_state_def,
      venom_state_component_equality]
QED
