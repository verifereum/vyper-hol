Theory fmpStageFmpStepsRetCaller
Ancestors
  fmpStageOpFrame fmpStageControl fmpStageOpBase fmpStageReclaimSound fmpStageRel
  fmpLowerReclaimPlan fmpLedgerProps livenessProofs ptrDiscipline
  o1PassContract venomExecSemantics venomState venomInst rich_list
  fmpStageFmpStepsRetInvokeCode fmpStageFmpStepsRetBind
  fmpStageFmpStepsRetAnalysis fmpStageFmpStepsRetFresh
  dftGasInvCallPartner frameHistoryCfg simplifyCfgPhiSemantics
  venomWfProps contextCodegenRel fmpReclaimDefs fmpAnalysisDefs list finite_map

(* The saved target frame is already past the current point's restore. *)
Theorem fmp_return_tidx_suc:
  (EL idx insts).inst_opcode <> DALLOCA /\
  (!rl rp. root = SOME (rl,rp) /\ lbl = rl ==> rp <> SUC idx) ==>
  fmp_stage_tidx plan root lbl insts (SUC idx) =
    SUC (fmp_stage_tidx plan root lbl insts idx +
         (if (lbl,idx) IN FDOM plan then 1 else 0))
Proof
  strip_tac >> simp[fmp_stage_tidx_def, GENLIST, SUM_SNOC] >>
  Cases_on `root`
  >- (simp[] >> decide_tac) >>
  rename1 `SOME x` >> PairCases_on `x` >>
  simp[] >> rw[] >> fs[arithmeticTheory.ADD_CLAUSES]
QED

Theorem fmp_return_caller_source_facts[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s ==>
  wf_function fn /\ ALL_DISTINCT inst.inst_outputs /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    EL s.vs_inst_idx bb.bb_instructions = inst
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `EVERY wf_function C.ctx_functions` by
    gvs[fmp_stage_ctx_def, o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[frame_reachable_dfs] >>
  `wf_function fn /\ ALL_DISTINCT inst.inst_outputs` by
    (conj_tac >- gvs[o1_fn_shape_def] >>
     irule all_distinct_flat_map_member >>
     qexists_tac `fn_insts fn` >> gvs[venomWfTheory.ssa_form_def, SF ETA_ss]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    gvs[venomWfTheory.wf_function_def, fn_labels_def] >>
  simp[] >> gvs[active_inst_def] >>
  metis_tac[venomExecProofsTheory.wf_lookup_block]
QED

Theorem fmp_return_caller:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\
  active_inst fn inst s /\ inst.inst_opcode = INVOKE /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_frame_rel sm fmp0 raw0 eb elo lo T fn fn' PG G tn.t_var s t /\
  ret.iret_adopt_fmp = NONE /\ ret'.iret_adopt_fmp = NONE /\
  ret'.iret_values = ret.iret_values /\
  bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s se)) = SOME s1 /\
  active_inst fn next (s1 with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?j t1. active_inst fn' j t /\ j.inst_outputs = inst.inst_outputs /\
    bind_outputs j.inst_outputs ret'.iret_values
      (adopt_return_fmp ret' (merge_callee_state t te)) = SOME t1 /\
    fmp_frame_rel sm fmp0 raw0 eb elo lo F fn fn' PG
      (DRESTRICT G (COMPL (set inst.inst_outputs)))
      (DRESTRICT tn.t_var (COMPL (set inst.inst_outputs)))
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  drule_all fmp_return_caller_source_facts >> strip_tac >>
  qpat_assum `fmp_frame_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [fmp_frame_rel_def, LET_THM]) >>
  drule_all fmp_return_saved_invoke_boundary >> strip_tac >>
  drule_all fmp_return_bind_caller >>
  disch_then (qspec_then `te` strip_assume_tac) >>

  `!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) ==>
     ~fmp_clears_marks infos inst` by
    (rpt gen_tac >> disch_tac >> irule fmp_return_saved_invoke_nonclearing >>
     simp[] >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`bb`,`fn'`,`s.vs_inst_idx`,`j`,`runner`,`t`] >> gvs[]) >>
  qexistsl_tac [`j`,`t1`] >> simp[] >>
  simp[fmp_frame_rel_def, LET_THM] >>
  qexistsl_tac [`infos`,`ctx`,`runner`] >>
  `s1.vs_current_bb = s.vs_current_bb /\ t1.vs_current_bb = t.vs_current_bb` by
    gvs[merge_callee_state_def, venom_state_component_equality] >>
  simp[] >>
  `!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
      s.vs_current_bb = rl ==> rp <> SUC s.vs_inst_idx` by metis_tac[] >>
  `fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
     s.vs_current_bb bb.bb_instructions (SUC s.vs_inst_idx) = SUC t.vs_inst_idx` by
    (irule EQ_TRANS >> irule_at (Pos hd) fmp_return_tidx_suc >> simp[] >>
     metis_tac[]) >>
  simp[] >>
  gvs[venom_state_component_equality, merge_callee_state_def] >>
  conj_tac >- gvs[fmp_params_rel_def] >>
  conj_tac >- (qpat_x_assum `!b z c id. _` mp_tac >> metis_tac[]) >>
  Cases_on `fmp_stage_root infos ctx fn` >> gvs[] >> PairCases_on `x` >> gvs[] >>
  drule fmp_return_analysis_suc >> simp[] >>
  disch_then (qspecl_then [`st`,`s.vs_inst_idx`,`bb`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `st'` >> simp[] >>
  conj_tac >- metis_tac[fmp_return_covers] >>
  `t.vs_current_bb = x0 /\ SUC s.vs_inst_idx < x1 <=>
   t.vs_current_bb = x0 /\ s.vs_inst_idx < x1` by
    (Cases_on `t.vs_current_bb = x0` >> gvs[] >> decide_tac) >>
  Cases_on `t.vs_current_bb = x0 /\ s.vs_inst_idx < x1` >> gvs[] >>
  csimp[] >> conj_tac
  >- (drule_all inv_bind_outputs_lookup_outside >>
      gvs[lookup_var_def, adopt_return_fmp_def]) >>
  qexists_tac `regions` >> simp[] >>
  irule fmp_return_ledger_bind >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`te`,`j.inst_outputs`,`ret'`,`ret'.iret_values`] >>
  simp[merge_callee_state_def] >> rpt strip_tac >>
  `MEM r.fr_mark (MAP (\r. r.fr_mark) regions)` by
    (simp[MEM_MAP] >> qexists_tac `r` >> simp[]) >>
  metis_tac[fmp_return_popped_outputs_fresh]
QED

