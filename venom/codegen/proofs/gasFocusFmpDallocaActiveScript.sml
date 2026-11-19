(* Reconstruct the active frame after the concrete DALLOCA expansion. *)
Theory gasFocusFmpDallocaActive
Ancestors
  gasFocusFmpCutSites gasFocusFmpDallocaLedger
  fmpStageFmpStepsDallocaData fmpStageFmpStepsLive fmpStageOpFrame
  fmpStageReclaimSound fmpStageRel fmpLowerSequenceExec
  o1LowerDloadRelocationKernel o1PassContract dftContractGas
  livenessProofs simplifyCfgDefs venomExecProofs contextCodegenRel
  ptrDiscipline venomInst venomState finite_map list words pair

Theorem dalloca_output_value[local]:
  inst.inst_opcode = DALLOCA /\ inst.inst_outputs = [out] /\
  w2n s.vs_fmp + z < dimword (:256) /\
  s1 = update_var out s.vs_fmp (s with vs_fmp := n2w (w2n s.vs_fmp+z)) /\
  sm1 = (if z=0 then sm else sm |+ ((w2n s.vs_fmp,z),(lo,inst.inst_id))) ==>
  fmp_value_rel sm1 (FLOOKUP (step_prov PG G inst s1) out)
    (op_taint (step_taint inst s s1 tn) (Var out)) s.vs_fmp (n2w lo)
Proof
  strip_tac >>
  simp[step_prov_def, out_prov_def, set_prov_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, fmp_value_rel_def] >>
  gvs[] >> Cases_on `z=0` >>
  simp[ld_value_agree_def, FLOOKUP_fmp_ld_sites, FLOOKUP_UPDATE, WORD_ADD_SUB2]
QED

Theorem dalloca_active_env[local]:
  wf_function fn /\ MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  s.vs_inst_idx < LENGTH bb.bb_instructions /\ inst = EL s.vs_inst_idx bb.bb_instructions /\
  inst.inst_opcode = DALLOCA /\ inst.inst_outputs = [out] /\
  fmp_env_rel sm fn (live_vars_at (liveness_analyze fn)
    s.vs_current_bb s.vs_inst_idx) G tn.t_var s t /\
  EVERY (\v. ~MEM v (fn_ir_vars fn)) [plus31;mask;aligned;runner] /\
  ALL_DISTINCT [plus31;mask;aligned;runner;out] /\
  w2n s.vs_fmp + z < dimword (:256) /\
  s1 = update_var out s.vs_fmp (s with vs_fmp := n2w (w2n s.vs_fmp+z)) /\
  t1 = (update_var runner (n2w (lo+z))
    (update_var out (n2w lo) (update_var aligned a
      (update_var mask m (update_var plus31 p t))))) with vs_inst_idx := j /\
  sm1 = (if z=0 then sm else sm |+ ((w2n s.vs_fmp,z),(lo,inst.inst_id))) /\
  (!k v. FLOOKUP sm k = SOME v ==> FLOOKUP sm1 k = SOME v) ==>
  fmp_env_rel sm1 fn (live_vars_at (liveness_analyze fn)
    s.vs_current_bb (SUC s.vs_inst_idx)) (step_prov PG G inst s1)
    (step_taint inst s s1 tn).t_var (s1 with vs_inst_idx := SUC s.vs_inst_idx) t1
Proof
  strip_tac >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb
               (SUC s.vs_inst_idx)) /\ v <> out ==>
       MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)` by
    (rpt strip_tac >> drule live_vars_at_propagate >> simp[] >>
     disch_then irule >> goal_assum (drule_at Any) >> gvs[inst_defs_def]) >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb
               (SUC s.vs_inst_idx)) ==> ~MEM v [plus31;mask;aligned;runner]` by
    (rpt strip_tac >> drule fmp_live_ir_vars >> gvs[EVERY_MEM] >> metis_tac[]) >>
  drule_all dalloca_output_value >> strip_tac >>
  irule fmp_dalloca_env_transition >>
  qexists_tac `G` >> goal_assum (drule_at Any) >>
  qexistsl_tac [`s`,`sm`,`t`,`tn.t_var`,`s.vs_fmp`,`n2w lo`] >>
  simp[] >>
  reverse conj_tac
  >- (gvs[op_taint_def] >>
      simp[step_prov_def, out_prov_def, set_prov_def, lookup_var_def,
           step_taint_def, set_var_taint_def, update_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >>
  qpat_x_assum `fmp_env_rel _ _ _ _ _ _ _` mp_tac >>
  simp[fmp_env_rel_def] >> disch_then drule >> strip_tac >>
  simp[update_var_def, FLOOKUP_UPDATE] >> rpt IF_CASES_TAC >> simp[]
QED

Theorem focus_fmp_dalloca_active_upto:
  o1_ctx_shape C /\ EVERY (o1_fn_row 3) C.ctx_functions /\
  raw0 = w2n vs.vs_fmp /\
  (!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
               dalloca_no_wrap inst s) /\
  frame_reachable vs C stk PG G tn fn inst s /\ gas_cut n vs s /\
  wf_function fn /\ ssa_form fn /\ all_reachable fn /\
  active_inst fn inst s /\ inst.inst_opcode = DALLOCA /\ inst.inst_outputs = [out] /\
  step_inst k C inst s = OK s1 /\
  fmp_frame_rel sm fmp0 raw0 eb elo lo T fn fn' PG G tn.t_var s t /\
  fmp_sites_ok sm fmp0 raw0 lo s.vs_fmp /\ eb = fmp_frame_base raw0 stk /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  fmp_stage_root infos ctx fn = SOME (rl,rp) /\
  ~(s.vs_current_bb = rl /\ s.vs_inst_idx < rp) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  fmp_base_analyze (fn_insts fn) = SOME env /\ fmp_reclaim_states infos fn = SOME states /\
  df_at NONE states s.vs_current_bb s.vs_inst_idx = SOME st /\
  MAP (\r. r.fr_mark) regions = SND (fmp_pop_at infos fn
    (liveness_analyze fn) env (s.vs_current_bb,s.vs_inst_idx) inst st) /\
  fmp_ledger_ok (fn_insts fn) env t lo regions /\ EVERY (\r. elo <= r.fr_lo) regions /\
  fmp_ledger_link sm eb lo regions /\ fmp_frame_covers sm env eb lo G /\
  ALL_DISTINCT [plus31;mask;aligned;runner;out] /\
  EVERY (\v. ~MEM v (fn_ir_vars fn)) [plus31;mask;aligned;runner] /\
  w2n s.vs_fmp + z < dimword (:256) /\ lo+z < dimword (:256) /\
  s1 = update_var out s.vs_fmp (s with vs_fmp := n2w (w2n s.vs_fmp+z)) /\
  t1 = (update_var runner (n2w (lo+z))
    (update_var out (n2w lo) (update_var aligned (n2w z)
      (update_var mask (~31w) (update_var plus31 (sz+31w) t)))))
    with vs_inst_idx := j /\
  j = fmp_stage_tidx (fmp_stage_plan infos ctx fn)
    (fmp_stage_root infos ctx fn) s.vs_current_bb bb.bb_instructions (SUC s.vs_inst_idx) /\
  sm1 = (if z=0 then sm else sm |+ ((w2n s.vs_fmp,z),(lo,inst.inst_id))) ==>
  fmp_frame_rel sm1 fmp0 raw0 eb elo (lo+z) F fn fn' PG
    (step_prov PG G inst s1) (step_taint inst s s1 tn).t_var
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) t1
Proof
  strip_tac >> drule_all focus_fmp_frame_sites_upto >> strip_tac >>
  drule o1_ctx_shape_wf_functions >> strip_tac >>
  drule_all frame_reachable_dfs >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb` by
    metis_tac[lookup_block_member_label] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\ inst = EL s.vs_inst_idx bb.bb_instructions` by
    (fs[active_inst_def] >> imp_res_tac wf_lookup_block >> gvs[]) >>
  qpat_x_assum `fmp_frame_rel _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [fmp_frame_rel_def, LET_THM]) >>
  `!b z c id. FLOOKUP sm (b,z) = SOME (c,id) ==>
    0 < z /\ b+z <= w2n s.vs_fmp /\ c+z <= lo` by
    metis_tac[fmp_sites_ok_def] >>
  `!k v. FLOOKUP sm k = SOME v ==> FLOOKUP sm1 k = SOME v` by
    (qx_gen_tac `key` >> qx_gen_tac `value` >>
     PairCases_on `key` >> PairCases_on `value` >> strip_tac >>
     Cases_on `z=0` >> simp[FLOOKUP_UPDATE] >> IF_CASES_TAC >> gvs[] >>
     qpat_x_assum `!b z c id. FLOOKUP sm _ = _ ==> 0 < z /\ _` drule >>
     simp[] >> decide_tac) >>
  `w2n s1.vs_fmp = w2n s.vs_fmp + z` by simp[update_var_def,w2n_n2w] >>
  `!v b z. FLOOKUP G v = SOME (b,z) /\ 0 < z ==> b+z <= w2n s.vs_fmp` by
    metis_tac[] >>
  `fmp_frame_covers sm1 env eb (lo+z) (step_prov PG G inst s1)` by
    (drule_all fmp_stage_covers_dalloca >> simp[Excl "w2n_11"]) >>
  `eb <= w2n s.vs_fmp` by metis_tac[] >>
  `df_at NONE states bb.bb_label s.vs_inst_idx = SOME st /\
   MAP (\r. r.fr_mark) regions = SND (fmp_pop_at infos fn
     (liveness_analyze fn) env (bb.bb_label,s.vs_inst_idx) inst st)` by (simp[] >> (gvs[])) >>
  drule_all (CONV_RULE (TOP_DEPTH_CONV Unwind.UNWIND_FORALL_CONV)
    focus_fmp_dalloca_ledger_push) >> simp[] >> strip_tac >>
  drule_all dalloca_active_env >> strip_tac >>
  drule_all fmp_dalloca_params_updates >> strip_tac >>
  simp[fmp_frame_rel_def] >> qexistsl [`infos`,`ctx`,`runner`] >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt conj_tac
  >- (gvs[fmp_frontier_rel_def] >> simp[w2n_n2w] >> decide_tac)
  >- (rpt gen_tac >> Cases_on `z=0` >- (simp[] >> metis_tac[]) >>
      simp[FLOOKUP_UPDATE] >> IF_CASES_TAC >> gvs[] >> metis_tac[])
  >- (strip_tac >> gvs[] >> decide_tac) >>
  qexists_tac `<|fr_mark := out;
                 fr_site := (EL s.vs_inst_idx bb.bb_instructions).inst_id;
                 fr_lo := lo; fr_hi := lo+z|> :: regions` >> simp[]
QED
