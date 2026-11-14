Theory bodyPtrSubscriptSeamMapCompose
Ancestors
  gasSummaryComposePtr gasSummaryComposePtrAll gasExemptCert fragGasPathPtr
  gasStorage gasSummary fragExec vyperStorageTrace vyperState

Theorem gas_outcome_bind_result_exec_ptr:
  gas_outcome_ptr D tops (ctx,func) PG cx st0
    (a : evaluation_state -> eval_result evaluation_result)
    (es,s0,G0,tn0) P Exit /\
  (!H res ee G tn t. P H res ee G tn t ==> ?v. res = INL v) /\
  (!H res ee gt r.
    valid_horizon cx st0 H ee.storage_trace /\ Exit H res ee gt r ==>
    ?ex. res = INR ex /\ R H (INR ex) ee gt r) /\
  (!v. storage_trace_frame (k v)) /\
  (!marks v mid G tn t.
    gas_marked_exec F (ctx,func) a (es,s0) marks (INL v) mid (OK t) /\
    (?H. valid_horizon cx st0 H mid.storage_trace) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
         gas_path_ptr (D H) 0 ctx func PG G0 tn0 s0 (LENGTH marks) G tn
           (OK t) /\
         P H (INL v) (mid with gas_obs := []) G tn t) ==>
    gas_outcome_ptr D tops (ctx,func) PG cx st0 (k v)
      (mid with gas_obs := [],t,G,tn) Q R) ==>
  gas_outcome_ptr D tops (ctx,func) PG cx st0 (bind a k)
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  mp_tac (Q.INST [`source` |-> `a`, `next` |-> `k`, `E` |-> `Exit`]
            gas_outcome_ptr_bind_all) >>
  impl_tac >- (
    rpt conj_tac
    >- simp[]
    >- (rpt strip_tac >> res_tac >> gvs[])
    >- (rpt strip_tac >>
        qpat_x_assum `!H res ee gt r. _ /\ Exit _ _ _ _ _ ==> _`
          drule_all >> simp[])
    >- simp[]
    >- (rpt strip_tac >> first_x_assum irule >> metis_tac[])
    >- (rpt strip_tac >> rewrite_tac[ignore_bind_def, bind_assoc] >>
        irule gas_exempt_cert_error_result >> fs[ignore_bind_def]) >>
    rpt strip_tac >> irule gas_exempt_cert_bind_result >>
    goal_assum (drule_at Any) >> simp[]) >>
  simp[]
QED

Theorem gas_outcome_result_cases_ptr:
  gas_outcome_ptr D tops (ctx,func) PG cx st0
    (a : evaluation_state -> eval_result evaluation_result)
    (es,s0,G0,tn0) P Exit /\
  (!H res ee G tn t. P H res ee G tn t ==> ?v. res = INL v) /\
  (!H res ee gt r.
    valid_horizon cx st0 H ee.storage_trace /\ Exit H res ee gt r ==>
    ?ex. res = INR ex /\ R H (INR ex) ee gt r) /\
  (!v. storage_trace_frame (k v)) /\
  (!marks v mid G tn t.
    gas_marked_exec F (ctx,func) a (es,s0) marks (INL v) mid (OK t) /\
    (?H. valid_horizon cx st0 H mid.storage_trace) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
         gas_path_ptr (D H) 0 ctx func PG G0 tn0 s0 (LENGTH marks) G tn
           (OK t) /\
         P H (INL v) (mid with gas_obs := []) G tn t) ==>
    gas_outcome_ptr D tops (ctx,func) PG cx st0 (bind a k)
      (es,s0,G0,tn0) Q R) ==>
  gas_outcome_ptr D tops (ctx,func) PG cx st0 (bind a k)
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ a _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_ptr_def])
  >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >>
      disj1_tac >> irule gas_bad_storage_at_bind_left >> simp[])
  >- (pop_assum (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_def]) >>
      reverse (Cases_on `?H. valid_horizon cx st0 H es_end.storage_trace`)
      >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >>
          disj1_tac >> irule gas_bad_storage_at_bind_left >> simp[] >>
          irule gas_bad_storage_at_no_horizon >> fs[] >> metis_tac[]) >>
      pop_assum strip_assume_tac >>
      first_assum drule >> strip_tac >> gvs[]
      >- (`?v. res = INL v` by metis_tac[] >> gvs[] >>
          qpat_x_assum `!marks v mid G tn t. _`
            (qspecl_then [`marks`, `v`, `es_end`, `G`, `tn`, `t`] irule) >>
          conj_tac
          >- (simp[gas_marked_exec_def, gas_marked_path_def] >>
              metis_tac[gas_path_ptr_erase]) >>
          conj_tac >- (qexists_tac `H` >> simp[]) >>
          gen_tac >> strip_tac >>
          qpat_x_assum
            `!H. valid_horizon cx st0 H es_end.storage_trace ==> _`
            (drule_then strip_assume_tac) >>
          gvs[exit_result_def]) >>
      `valid_horizon cx st0 H (es_end with gas_obs := []).storage_trace` by
        simp[] >>
      qpat_x_assum `!H res ee gt r. _ /\ Exit _ _ _ _ _ ==> _`
        (fn th => assume_tac th >> drule_all_then strip_assume_tac th) >>
      gvs[] >>
      rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >>
      disj2_tac >> disj1_tac >>
      mp_tac (Q.INST [`fin` |-> `es_end`, `source` |-> `a`, `next` |-> `k`,
                      `exc` |-> `ex`]
                gas_summary_ptr_at_bind_exception) >>
      impl_tac >- (
        fs[] >> gen_tac >> strip_tac >>
        `valid_horizon cx st0 H' (es_end with gas_obs := []).storage_trace`
          by simp[] >>
        qpat_x_assum `!H. valid_horizon cx st0 H es_end.storage_trace ==> _`
          (drule_then strip_assume_tac) >>
        gvs[exit_result_def] >>
        qpat_x_assum `!H res ee gt r. _ /\ Exit _ _ _ _ _ ==> _`
          (drule_all_then strip_assume_tac) >> gvs[]) >>
      simp[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_result >> simp[]
QED
