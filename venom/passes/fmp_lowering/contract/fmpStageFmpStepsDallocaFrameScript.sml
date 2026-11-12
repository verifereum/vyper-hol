Theory fmpStageFmpStepsDallocaFrame
Ancestors
  fmpStageControl fmpStageOpBase fmpStageReclaimSound fmpStageRel
  fmpLowerReclaimPlan fmpLowerSequenceExec fmpLedgerProps fmpAliasProps
  fmpReclaimDefs fmpAnalysisDefs venomState finite_map words list

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
