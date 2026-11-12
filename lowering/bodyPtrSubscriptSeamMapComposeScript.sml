Theory bodyPtrSubscriptSeamMapCompose
Ancestors
  gasSummaryComposePtr gasExemptCert fragGasPathPtr vyperState

Theorem gas_outcome_bind_result_exec_ptr:
  gas_outcome_ptr D tops (ctx,func) PG
    (a : evaluation_state -> eval_result evaluation_result)
    (es,s0,G0,tn0) P Exit /\
  (!res ee G tn t. P res ee G tn t ==> ?v. res = INL v) /\
  (!res ee gt r. Exit res ee gt r ==>
    ?ex. res = INR ex /\ R (INR ex) ee gt r) /\
  (!marks v mid G tn t.
    gas_marked_exec_ptr D (ctx,func) PG a (es,s0,G0,tn0)
      marks (INL v) mid G tn (OK t) /\
    P (INL v) (mid with gas_obs := []) G tn t ==>
    gas_outcome_ptr D tops (ctx,func) PG (k v)
      (mid with gas_obs := [],t,G,tn) Q R) ==>
  gas_outcome_ptr D tops (ctx,func) PG (bind a k)
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ a _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_ptr_def])
  >- (pop_assum (strip_assume_tac o
        SIMP_RULE (srw_ss()) [gas_summary_ptr_at_marked])
      >- (`?v. res = INL v` by metis_tac[] >> gvs[] >>
          irule gas_outcome_ptr_bind_normal >>
          goal_assum (drule_at Any) >> conj_tac
          >- (rpt strip_tac >> irule gas_exempt_cert_bind_result >>
              goal_assum (drule_at Any) >> simp[]) >>
          first_x_assum irule >> metis_tac[]) >>
      `?ex. res = INR ex /\
         R (INR ex) (es_end with gas_obs := []) (G,tn) r` by metis_tac[] >>
      gvs[] >> rewrite_tac[gas_outcome_ptr_def] >>
      qexists_tac `marks` >> disj1_tac >>
      irule gas_summary_ptr_at_bind_exception >>
      goal_assum (drule_at Any) >> simp[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_result >> simp[]
QED

Theorem gas_outcome_result_cases_ptr:
  gas_outcome_ptr D tops (ctx,func) PG
    (a : evaluation_state -> eval_result evaluation_result)
    (es,s0,G0,tn0) P Exit /\
  (!res ee G tn t. P res ee G tn t ==> ?v. res = INL v) /\
  (!res ee gt r. Exit res ee gt r ==>
    ?ex. res = INR ex /\ R (INR ex) ee gt r) /\
  (!marks v mid G tn t.
    gas_marked_exec_ptr D (ctx,func) PG a (es,s0,G0,tn0)
      marks (INL v) mid G tn (OK t) /\
    P (INL v) (mid with gas_obs := []) G tn t ==>
    gas_outcome_ptr D tops (ctx,func) PG (bind a k)
      (es,s0,G0,tn0) Q R) ==>
  gas_outcome_ptr D tops (ctx,func) PG (bind a k)
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ a _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_ptr_def])
  >- (pop_assum (strip_assume_tac o
        SIMP_RULE (srw_ss()) [gas_summary_ptr_at_marked])
      >- (`?v. res = INL v` by metis_tac[] >> gvs[] >>
          first_x_assum irule >> metis_tac[]) >>
      `?ex. res = INR ex /\
         R (INR ex) (es_end with gas_obs := []) (G,tn) r` by metis_tac[] >>
      gvs[] >> rewrite_tac[gas_outcome_ptr_def] >>
      qexists_tac `marks` >> disj1_tac >>
      irule gas_summary_ptr_at_bind_exception >>
      goal_assum (drule_at Any) >> simp[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_result >> simp[]
QED
