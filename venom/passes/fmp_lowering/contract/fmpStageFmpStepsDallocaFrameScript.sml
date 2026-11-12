Theory fmpStageFmpStepsDallocaFrame
Ancestors
  fmpStageControl fmpStageOpBase fmpStageReclaimSound fmpStageRel
  fmpLowerReclaimPlan fmpLowerSequenceExec fmpLedgerProps fmpAliasProps
  fmpReclaimDefs fmpAnalysisDefs venomState finite_map words list

Theorem fmp_dalloca_analysis_suc[local]:
  fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  MEM bb fn.fn_blocks /\ idx < LENGTH bb.bb_instructions /\
  inst = EL idx bb.bb_instructions /\
  inst.inst_opcode = DALLOCA /\ inst.inst_outputs = [out] /\
  df_at NONE states bb.bb_label idx = SOME st ==>
  ?st'. df_at NONE states bb.bb_label (SUC idx) = SOME st' /\
    st'.frs_stack = out :: SND (fmp_pop_at infos fn
      (liveness_analyze fn) env (bb.bb_label,idx) inst st)
Proof
  strip_tac >> drule_all fmp_reclaim_states_df_at_suc >>
  simp[fmp_transfer_def, fmp_reclaim_step_def] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  `~fmp_clears_marks infos (EL idx bb.bb_instructions)` by
    metis_tac[fmp_dalloca_not_clear] >>
  drule_all fmp_apply_effect_dalloca_stack >> simp[]
QED

Theorem fmp_dalloca_ledger_push[local]:
  fmp_ledger_ok insts env t lo regions /\
  lo + z < dimword (:256) /\
  fmp_dalloca_query insts env out = SOME site /\
  ALL_DISTINCT [plus31;mask;aligned;runner;out] /\
  EVERY (\v. ~MEM v (MAP (\r. r.fr_mark) regions))
    [plus31;mask;aligned;runner;out] /\
  t1 = (update_var runner (n2w (lo+z))
        (update_var out (n2w lo)
         (update_var aligned a (update_var mask m (update_var plus31 p t)))))
        with vs_inst_idx := idx ==>
  fmp_ledger_ok insts env t1 (lo+z)
    (<| fr_mark := out; fr_site := site; fr_lo := lo; fr_hi := lo+z |> :: regions)
Proof
  strip_tac >> gvs[] >>
  simp[Once fmp_ledger_ok_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  irule fmp_ledger_frame >> qexists_tac `t` >> simp[] >>
  gvs[EVERY_MEM, MEM_MAP, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> rpt IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem fmp_dalloca_ledger_link[local]:
  fmp_ledger_link sm eb lo rs /\
  (!b n c id. FLOOKUP sm (b,n) = SOME (c,id) ==> 0 < n /\ c+n <= lo) /\
  eb <= b /\ (rs <> [] ==> (LAST rs).fr_lo <= lo) /\
  sm1 = (if z = 0 then sm else sm |+ ((b,z),(lo,site))) ==>
  fmp_ledger_link sm1 eb (lo+z)
    (<|fr_mark := out; fr_site := site; fr_lo := lo; fr_hi := lo+z|> :: rs)
Proof
  strip_tac >>
  `!b n c id. FLOOKUP sm (b,n) = SOME (c,id) ==> c < lo` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  Cases_on `rs = []`
  >- (gvs[fmp_ledger_link_def] >> rpt strip_tac >>
      Cases_on `z = 0` >> gvs[FLOOKUP_UPDATE, AllCaseEqs()] >>
      metis_tac[arithmeticTheory.NOT_LESS]) >>
  gvs[fmp_ledger_link_def, LAST_CONS_cond] >> rpt strip_tac >>
  Cases_on `z = 0` >> gvs[FLOOKUP_UPDATE, AllCaseEqs()] >>
  simp[RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  metis_tac[arithmeticTheory.NOT_LESS]
QED

Theorem fmp_dalloca_env_transition[local]:
  fmp_env_rel sm fn live G tv s t /\
  (!v. MEM v live' /\ v <> out ==> MEM v live) /\
  (!v. v <> out ==> FLOOKUP s'.vs_vars v = FLOOKUP s.vs_vars v) /\
  FLOOKUP s'.vs_vars out = SOME xout /\
  FLOOKUP t'.vs_vars out = SOME yout /\
  (!v x. v <> out /\ FLOOKUP s.vs_vars v = SOME x ==>
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
  qpat_x_assum `!v x. FLOOKUP s.vs_vars v = SOME x ==> _`
    (drule_then strip_assume_tac) >>
  qexists_tac `y` >> conj_tac >- metis_tac[] >> strip_tac >>
  `fmp_value_rel sm (FLOOKUP G v)
    (op_taint (entry_taint with t_var := tv) (Var v)) x y` by metis_tac[] >>
  gvs[fmp_value_rel_def] >>
  Cases_on `FLOOKUP G v` >>
  gvs[o1LowerDloadRelocationKernelTheory.ld_value_agree_def] >>
  PairCases_on `x'` >> gvs[FLOOKUP_fmp_ld_sites, AllCaseEqs()] >>
  metis_tac[]
QED
