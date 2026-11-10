Theory aggregateCountedOutcomeFacts
Ancestors
  aggregateCountedOutcome gasOutcome gasSummary fragGasMode fragGasPath
  vyperState venomState

Theorem counted_outcome_normal_facts:
  gas_outcome memory tops (ctx,func) source (es,s0) Q R ==>
  gas_outcome memory tops (ctx,func) source (es,s0)
    (\res ee t. Q res ee t /\ ee.gas_obs = [] /\ ~t.vs_halted /\
       ?gs. source (es with gas_obs := gs) = (res,ee)) R
Proof
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN assume_tac))
  >- (qexists_tac `marks` >> disj1_tac >>
      fs[gas_summary_at_def] >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      rpt strip_tac >> gvs[] >>
      disj1_tac >> conj_tac
      >- metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
      fs[gas_marked_exec_def] >>
      first_x_assum (qspec_then `[]` mp_tac) >> simp[] >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >> first_assum ACCEPT_TAC
QED
