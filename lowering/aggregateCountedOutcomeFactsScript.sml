Theory aggregateCountedOutcomeFacts
Ancestors
  aggregateCountedOutcome gasOutcome gasSummary fragGasMode fragGasPath
  vyperState venomState

Theorem counted_outcome_normal_facts:
  gas_outcome memory tops (ctx,func) cx st0 source (es,s0) Q R ==>
  gas_outcome memory tops (ctx,func) cx st0 source (es,s0)
    (\H res ee t. Q H res ee t /\ ee.gas_obs = [] /\ ~t.vs_halted /\
       ?gs. source (es with gas_obs := gs) = (res,ee)) R
Proof
  rewrite_tac[gas_outcome_def] >> BETA_TAC >>
  disch_then (qx_choose_then `marks` strip_assume_tac)
  >- (qexists_tac `marks` >> disj1_tac >> first_assum ACCEPT_TAC)
  >- (qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      fs[gas_summary_at_def] >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >> gvs[] >>
      disj1_tac >>
      `~t.vs_halted` by
        metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
      `?gs. source (es with gas_obs := gs) = (res, es_end with gas_obs := [])` by
        (fs[gas_marked_exec_def] >>
         first_x_assum (qspec_then `[]` mp_tac) >> simp[] >> metis_tac[]) >>
      rpt strip_tac >> simp[] >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >> disj2_tac >> metis_tac[]
QED
