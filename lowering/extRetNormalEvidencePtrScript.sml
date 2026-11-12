Theory extRetNormalEvidencePtr
Ancestors
  fragGasPathPtr fragGasSeqPtr gasSummary vyperState

Theorem gas_outcome_ptr_normal_evidence:
  gas_outcome_ptr D tops (ctx,func) PG source (es,s,G,tn) P R ==>
  gas_outcome_ptr D tops (ctx,func) PG source (es,s,G,tn)
    (\res ee G1 tn1 t. P res ee G1 tn1 t /\ ~t.vs_halted /\
       (?gs. source (es with gas_obs := gs) = (res,ee)) /\
       (?n. gas_path_ptr D 0 ctx func PG G tn s n G1 tn1 (OK t))) R
Proof
  rewrite_tac[gas_outcome_ptr_def] >>
  disch_then (qx_choose_then `marks` mp_tac) >>
  disch_then DISJ_CASES_TAC
  >- (qexists_tac `marks` >> disj1_tac >>
      fs[gas_summary_ptr_at_def] >>
      qexistsl_tac [`res`, `es_end`, `G'`, `tn'`, `r`] >> simp[] >>
      disj1_tac >> conj_tac
      >- metis_tac[gas_path_ptr_ok_not_halted] >>
      reverse conj_tac >- (qexists_tac `LENGTH marks` >> gvs[]) >>
      qexists_tac `gas_explicit marks s.vs_gas_readings` >>
      first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  qexists_tac `marks` >> disj2_tac >> first_assum ACCEPT_TAC
QED
