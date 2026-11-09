(* Expose the actual marked prefix to its continuation.  This deliberately
   does not replace it with another outcome having independently chosen marks. *)
Theory bodyPtrMakeArrayConsBind
Ancestors
  gasSummaryComposePtr fragGasPathPtr gasExemptCert gasSummary vyperState

Theorem literal_marked_exec_end_gas_obs:
  gas_marked_exec_ptr D (ctx,func) PG source start marks res
    (ee with gas_obs := gs) G tn r <=>
  gas_marked_exec_ptr D (ctx,func) PG source start marks res ee G tn r
Proof
  PairCases_on `start` >> simp[gas_marked_exec_ptr_def]
QED

Theorem literal_result_bind_outcome_ptr:
  gas_outcome_ptr D tops (ctx,func) PG
    (a : evaluation_state -> eval_result evaluation_result) (es,s0,G0,tn0)
    (\res ee G tn t. ?v. res = INL v /\ P v ee G tn t)
    (\res ee gt r. ?exc. res = INR exc /\ R (INR exc) ee gt r) /\
  (!marks v ee G tn t.
    gas_marked_exec_ptr D (ctx,func) PG a (es,s0,G0,tn0)
      marks (INL v) ee G tn (OK t) /\
    ee.gas_obs = [] /\ P v ee G tn t ==>
    gas_outcome_ptr D tops (ctx,func) PG
      (k v : evaluation_state -> 'b evaluation_result) (ee,t,G,tn) Q R) ==>
  gas_outcome_ptr D tops (ctx,func) PG (bind a k) (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >>
  disch_then (qx_choose_then `left` strip_assume_tac)
  >- (gvs[] >>
      first_x_assum (qspecl_then
        [`left`, `v`, `es_end with gas_obs := []`, `G`, `tn`, `t`] mp_tac) >>
      (impl_tac >- fs[literal_marked_exec_end_gas_obs]) >>
      rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >>
      disch_then (qx_choose_then `right` strip_assume_tac)
      >- (qexists `left ++ right` >> disj1_tac >>
          metis_tac[gas_marked_exec_ptr_bind_normal])
      >- (qexists `left ++ right` >> disj1_tac >>
          metis_tac[gas_marked_exec_ptr_bind_normal]) >>
      qexists `left ++ right` >> disj2_tac >>
      rewrite_tac[ignore_bind_def, bind_assoc] >>
      irule_at Any gas_exempt_cert_bind_result >>
      simp[GSYM ignore_bind_def] >> metis_tac[gas_marked_exec_ptr_exec])
  >- (gvs[] >> qexists `left` >> disj1_tac >>
      metis_tac[gas_marked_exec_ptr_bind_exception]) >>
  qexists `left` >> disj2_tac >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule_at Any gas_exempt_cert_error_result >>
  simp[GSYM ignore_bind_def] >> metis_tac[]
QED
