Theory fmpStageFmpStepsDallocaData
Ancestors
  fmpStageRel fmpStageOpBase fmpStageReclaimSound
  o1LowerDloadRelocationKernel finite_map words list
  livenessTerminationProofs livenessInvariantProofs fmpStepSupply
  frameHistoryCfg simplifyCfgPhiSemantics venomWfProps livenessProofs
  livenessDefs venomInst ptrDiscipline o1PassContract contextCodegenRel
  venomExecProofs decoderGhostFramePtr

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

Theorem fmp_dalloca_live_ir[local]:
  MEM v (live_vars_at (liveness_analyze fn) lbl i) ==> MEM v (fn_ir_vars fn)
Proof
  strip_tac >>
  `lv_bounded fn.fn_blocks (liveness_analyze fn)` by
    metis_tac[liveness_recompute_invariant, lv_inv_def, liveness_analyze_def] >>
  `MEM v (livenessDefs$fn_all_vars fn.fn_blocks)` by
    metis_tac[lv_bounded_read, live_vars_at_def] >>
  gvs[livenessDefsTheory.fn_all_vars_def, MEM_FLAT, MEM_MAP,
      fn_ir_vars_member, inst_defs_def] >> metis_tac[]
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
  >- (rpt strip_tac >> drule fmp_dalloca_live_ir >>
      gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  `EVERY wf_function C.ctx_functions` by
    gvs[fmp_stage_ctx_def, o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  drule_all frame_reachable_cfg_histories >> strip_tac >>
  drule frame_history_cfg_invariant >> simp[] >> strip_tac >>
  `wf_function fn` by gvs[o1_fn_shape_def] >>
  `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    (gvs[frame_history_cfg_def] >> irule fn_reachable_in_cfg_dfs_pre >> simp[] >>
     irule scfg_path_member_reachable >> qexists_tac `history_visits h` >>
     simp[] >> metis_tac[rich_listTheory.MEM_LAST_NOT_NIL]) >>
  gvs[active_inst_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    metis_tac[wf_lookup_block] >>
  rpt strip_tac >> drule live_vars_at_propagate >> simp[inst_defs_def] >>
  disch_then irule >> simp[] >> metis_tac[]
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
  simp[ld_value_agree_def, FLOOKUP_fmp_ld_sites, FLOOKUP_UPDATE] >>
  wordsLib.WORD_DECIDE_TAC
QED
