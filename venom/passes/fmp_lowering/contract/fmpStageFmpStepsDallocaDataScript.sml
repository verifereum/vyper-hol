Theory fmpStageFmpStepsDallocaData
Ancestors
  fmpStageFmpStepsLive fmpStageOpFrame fmpStageRel fmpStageOpBase fmpStageReclaimSound
  o1LowerDloadRelocationKernel finite_map words list
  livenessTerminationProofs livenessInvariantProofs fmpStepSupply
  frameHistoryCfg simplifyCfgPhiSemantics venomWfProps livenessProofs
  livenessDefs venomInst ptrDiscipline o1PassContract contextCodegenRel
  venomExecProofs decoderGhostFramePtr venomState

Theorem fmp_dalloca_env_transition:
  fmp_env_rel sm fn live G tv s t /\
  (!v. MEM v live' /\ v <> out ==> MEM v live) /\
  (!v. v <> out ==> FLOOKUP s'.vs_vars v = FLOOKUP s.vs_vars v) /\
  FLOOKUP s'.vs_vars out = SOME xout /\
  FLOOKUP t'.vs_vars out = SOME yout /\
  (!v x. v <> out /\ FLOOKUP s.vs_vars v = SOME x ==>
    ?y. FLOOKUP t'.vs_vars v = SOME y) /\
  (!v. v <> out /\ MEM v live' /\ ~retpc_var fn v ==>
    FLOOKUP t'.vs_vars v = FLOOKUP t.vs_vars v) /\
  (!v. v <> out ==> FLOOKUP G' v = FLOOKUP G v /\
    op_taint (entry_taint with t_var := tv') (Var v) =
    op_taint (entry_taint with t_var := tv) (Var v)) /\
  (!k v. FLOOKUP sm k = SOME v ==> FLOOKUP sm' k = SOME v) /\
  fmp_value_rel sm' (FLOOKUP G' out)
    (op_taint (entry_taint with t_var := tv') (Var out)) xout yout ==>
  fmp_env_rel sm' fn live' G' tv' s' t'
Proof
  simp[fmp_env_rel_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `v = out` >- (gvs[] >> metis_tac[]) >>
  `FLOOKUP s.vs_vars v = SOME x` by metis_tac[] >>
  `?y. FLOOKUP t'.vs_vars v = SOME y` by metis_tac[] >>
  qexists_tac `y` >> simp[] >> strip_tac >>
  qpat_x_assum `!v x. FLOOKUP s.vs_vars v = SOME x ==> _`
    (drule_then strip_assume_tac) >>
  `FLOOKUP t'.vs_vars v = FLOOKUP t.vs_vars v` by
    (qpat_x_assum `!v. v <> out /\ MEM v live' /\ _ ==> _` irule >> simp[]) >>
  `MEM v live` by metis_tac[] >>
  gvs[] >>
  gvs[fmp_value_rel_def] >>
  Cases_on `FLOOKUP G v` >>
  gvs[ld_value_agree_def] >>
  PairCases_on `x'` >> gvs[FLOOKUP_fmp_ld_sites, AllCaseEqs()] >>
  qpat_x_assum `!k v. FLOOKUP sm k = SOME v ==> _` drule >>
  strip_tac >> simp[]
QED

Theorem fmp_dalloca_live_transport[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_outputs = [out] /\
  EVERY (\v. ~MEM v (fn_ir_vars fn)) scratch ==>
  (!v. MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb
    (SUC s.vs_inst_idx)) /\ v <> out ==>
    MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)) /\
  (!v. MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb
    (SUC s.vs_inst_idx)) ==> ~MEM v scratch)
Proof
  strip_tac >> reverse conj_tac
  >- (rpt strip_tac >> drule fmp_live_ir_vars >>
      gvs[EVERY_MEM] >> metis_tac[]) >>
  rpt strip_tac >> `~MEM v inst.inst_outputs` by gvs[] >>
  drule_all fmp_live_ordinary_suc >> simp[]
QED

Theorem fmp_dalloca_output_value[local]:
  inst.inst_opcode = DALLOCA /\ inst.inst_outputs = [out] /\
  w2n s.vs_fmp + z < dimword (:256) /\
  s1 = update_var out s.vs_fmp
    (s with vs_fmp := n2w (w2n s.vs_fmp+z)) /\
  sm1 = (if z=0 then sm else sm |+ ((w2n s.vs_fmp,z),(lo,inst.inst_id))) ==>
  fmp_value_rel sm1 (FLOOKUP (step_prov PG G inst s1) out)
    (op_taint (step_taint inst s s1 tn) (Var out)) s.vs_fmp (n2w lo)
Proof
  strip_tac >>
  simp[step_prov_def, out_prov_def, set_prov_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, fmp_value_rel_def] >>
  gvs[] >> Cases_on `z=0` >>
  simp[ld_value_agree_def, FLOOKUP_fmp_ld_sites, FLOOKUP_UPDATE,
       WORD_ADD_SUB2]
QED

Theorem fmp_dalloca_env_updates:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = DALLOCA /\ inst.inst_outputs = [out] /\
  fmp_env_rel sm fn (live_vars_at (liveness_analyze fn)
    s.vs_current_bb s.vs_inst_idx) G tn.t_var s t /\
  EVERY (\v. ~MEM v (fn_ir_vars fn)) [plus31;mask;aligned] /\
  ~MEM runner (fn_ir_vars fn) /\
  ALL_DISTINCT [plus31;mask;aligned;runner;out] /\
  w2n s.vs_fmp + z < dimword (:256) /\
  s1 = update_var out s.vs_fmp
    (s with vs_fmp := n2w (w2n s.vs_fmp+z)) /\
  t1 = (update_var runner (n2w (lo+z))
    (update_var out (n2w lo) (update_var aligned a
      (update_var mask m (update_var plus31 p t))))) with vs_inst_idx := idx /\
  sm1 = (if z=0 then sm else sm |+ ((w2n s.vs_fmp,z),(lo,inst.inst_id))) /\
  (!k v. FLOOKUP sm k = SOME v ==> FLOOKUP sm1 k = SOME v) ==>
  fmp_env_rel sm1 fn (live_vars_at (liveness_analyze fn)
    s.vs_current_bb (SUC s.vs_inst_idx)) (step_prov PG G inst s1)
    (step_taint inst s s1 tn).t_var
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) t1
Proof
  strip_tac >>
  drule_all fmp_dalloca_live_transport >> strip_tac >>
  irule fmp_dalloca_env_transition >>
  qexists_tac `G` >>
  goal_assum (drule_at Any) >>
  qexists_tac `s` >>
  qexists_tac `sm` >>
  qexists_tac `t` >>
  qexistsl_tac [`tn.t_var`, `s.vs_fmp`, `n2w lo`] >>
  `fmp_value_rel sm1 (FLOOKUP (step_prov PG G inst s1) out)
    (op_taint (step_taint inst s s1 tn) (Var out)) s.vs_fmp (n2w lo)` by
    (irule fmp_dalloca_output_value >> metis_tac[]) >>
  simp[] >>
  reverse conj_tac >-
    (gvs[op_taint_def] >>
     simp[step_prov_def, out_prov_def, set_prov_def, lookup_var_def,
       step_taint_def, set_var_taint_def, update_var_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >>
     `MEM v (fn_ir_vars fn)` by metis_tac[fmp_live_ir_vars] >>
     gvs[EVERY_MEM] >> metis_tac[]) >>
  rpt strip_tac >>
  qpat_x_assum `fmp_env_rel _ _ _ _ _ _ _` mp_tac >>
  simp[fmp_env_rel_def] >> disch_then drule >> strip_tac >>
  simp[update_var_def, FLOOKUP_UPDATE] >>
  rpt IF_CASES_TAC >> simp[]
QED

Theorem fmp_dalloca_params_updates:
  fmp_params_rel sm PG s t /\
  (!k v. FLOOKUP sm k = SOME v ==> FLOOKUP sm1 k = SOME v) /\
  s1 = update_var out s.vs_fmp
    (s with vs_fmp := n2w (w2n s.vs_fmp+z)) /\
  t1 = (update_var runner (n2w (lo+z))
    (update_var out (n2w lo) (update_var aligned a
      (update_var mask m (update_var plus31 p t))))) with vs_inst_idx := idx ==>
  fmp_params_rel sm1 PG (s1 with vs_inst_idx := SUC s.vs_inst_idx) t1
Proof
  simp[update_var_def, fmp_params_rel_def] >> strip_tac >>
  rpt strip_tac >> first_x_assum drule >>
  simp[fmp_value_rel_def] >> strip_tac >> simp[] >>
  Cases_on `if k < LENGTH PG then EL k PG else NONE` >>
  gvs[ld_value_agree_def] >> disj2_tac >>
  rename1 `FLOOKUP (fmp_ld_sites sm) site = SOME (b,c,n)` >>
  PairCases_on `site` >> gvs[FLOOKUP_fmp_ld_sites, AllCaseEqs()] >>
  qpat_x_assum `!k v. FLOOKUP sm k = SOME v ==> _` drule >>
  strip_tac >> qexistsl_tac [`b`, `c`, `n`] >>
  simp[FLOOKUP_fmp_ld_sites]
QED
