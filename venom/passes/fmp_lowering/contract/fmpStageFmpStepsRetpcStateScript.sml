Theory fmpStageFmpStepsRetpcState
Ancestors
  fmpStageFmpStepsRetpcPreservation livenessProofs cfgWf venomWfProps
  venomExecProofs o1LowerDloadShared o1LowerDloadRelocationKernel
  fmpStageRel ptrDiscipline venomState venomInst codegenRel
  contextCodegenRel venomWf cfgDefs livenessDefs
  finite_map list pred_set

Theorem fmp_retpc_prov:
  inst.inst_opcode = RETPC_PARAM /\ inst.inst_outputs = [pc] ==>
  step_prov PG G inst s1 = DRESTRICT G (COMPL {pc})
Proof
  simp[step_prov_def, out_prov_def, set_prov_def]
QED

Theorem fmp_retpc_env_next:
  fmp_env_rel sm fn old G tv s t /\ retpc_var fn pc /\
  (!v. MEM v next /\ ~retpc_var fn v ==> MEM v old) ==>
  fmp_env_rel sm fn next (DRESTRICT G (COMPL {pc}))
    (set_var_taint tv [pc] {})
    ((update_var pc x s) with vs_inst_idx := si)
    ((update_var pc y t) with vs_inst_idx := ti)
Proof
  simp[fmp_env_rel_def, update_var_def, FLOOKUP_UPDATE,
       set_var_taint_def, FLOOKUP_DRESTRICT, op_taint_def] >>
  rpt strip_tac >> Cases_on `v = pc` >> gvs[] >>
  first_x_assum drule >> strip_tac >> goal_assum (drule_at Any) >>
  metis_tac[]
QED

Theorem fmp_retpc_env_runner_next:
  fmp_env_rel sm fn old G tv s t /\ retpc_var fn pc /\
  (!v. MEM v next /\ ~retpc_var fn v ==> MEM v old /\ v <> runner) ==>
  fmp_env_rel sm fn next (DRESTRICT G (COMPL {pc}))
    (set_var_taint tv [pc] {})
    ((update_var pc x s) with vs_inst_idx := si)
    ((update_var pc y (update_var runner z t)) with vs_inst_idx := ti)
Proof
  simp[fmp_env_rel_def, update_var_def, FLOOKUP_UPDATE,
       set_var_taint_def, FLOOKUP_DRESTRICT, op_taint_def] >>
  rpt strip_tac >> Cases_on `v = pc` >> gvs[] >>
  Cases_on `v = runner` >> gvs[]
  >- metis_tac[] >>
  first_x_assum drule >> strip_tac >> goal_assum (drule_at Any) >>
  metis_tac[]
QED

Theorem fmp_retpc_live_next:
  wf_function fn /\ all_reachable fn /\ active_inst fn inst s /\
  inst.inst_outputs = [pc] /\
  MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb
          (SUC s.vs_inst_idx)) /\ v <> pc ==>
  MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
Proof
  strip_tac >>
  `fn_reachable fn s.vs_current_bb` by
    (gvs[all_reachable_def, active_inst_def] >> metis_tac[]) >>
  `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[fn_reachable_in_cfg_dfs_pre] >>
  gvs[active_inst_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >>
     gvs[venomWfTheory.wf_function_def, fn_labels_def]) >>
  drule live_vars_at_propagate >> simp[] >>
  disch_then irule >> goal_assum (drule_at Any) >>
  simp[inst_defs_def]
QED

Theorem fmp_retpc_env_step:
  wf_function fn /\ all_reachable fn /\ active_inst fn inst s /\
  inst.inst_opcode = RETPC_PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [pc] /\ retpc_var fn pc /\
  fmp_env_rel sm fn
    (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
    G tn.t_var s t ==>
  fmp_env_rel sm fn
    (live_vars_at (liveness_analyze fn) s.vs_current_bb (SUC s.vs_inst_idx))
    (step_prov PG G inst (update_var pc x s))
    (step_taint inst s (update_var pc x s) tn).t_var
    ((update_var pc x s) with vs_inst_idx := si)
    ((update_var pc y t) with vs_inst_idx := ti)
Proof
  strip_tac >> drule_all fmp_retpc_prov >> disch_then (qspec_then `update_var pc x s` assume_tac) >>
  simp[fmp_retpc_taint] >>
  irule fmp_retpc_env_next >> simp[] >>
  metis_tac[fmp_retpc_live_next]
QED

Theorem fmp_retpc_env_runner_step:
  wf_function fn /\ all_reachable fn /\ active_inst fn inst s /\
  inst.inst_opcode = RETPC_PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [pc] /\ retpc_var fn pc /\
  (!v. MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb
               (SUC s.vs_inst_idx)) /\ ~retpc_var fn v ==> v <> runner) /\
  fmp_env_rel sm fn
    (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
    G tn.t_var s t ==>
  fmp_env_rel sm fn
    (live_vars_at (liveness_analyze fn) s.vs_current_bb (SUC s.vs_inst_idx))
    (step_prov PG G inst (update_var pc x s))
    (step_taint inst s (update_var pc x s) tn).t_var
    ((update_var pc x s) with vs_inst_idx := si)
    ((update_var pc y (update_var runner z t)) with vs_inst_idx := ti)
Proof
  strip_tac >> drule_all fmp_retpc_prov >> disch_then (qspec_then `update_var pc x s` assume_tac) >>
  simp[fmp_retpc_taint] >>
  irule fmp_retpc_env_runner_next >> simp[] >>
  metis_tac[fmp_retpc_live_next]
QED

Theorem fmp_retpc_shared_write:
  ld_shared_agree D A (tn with t_var := vars)
    (s with <|vs_vars := sv; vs_inst_idx := si|>)
    (t with <|vs_vars := tv; vs_inst_idx := ti|>) = ld_shared_agree D A tn s t
Proof
  simp[ld_shared_agree_def]
QED
