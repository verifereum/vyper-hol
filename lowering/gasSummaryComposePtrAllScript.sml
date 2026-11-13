(* Bind for gas_outcome_ptr where the continuation needs the source's
 * normal post at every horizon at once (the next segment's per-H premise),
 * not at one horizon as gasSummaryComposePtr's gas_outcome_ptr_bind gives.
 *
 * TOP-LEVEL:
 *   gas_outcome_ptr_bind_all
 *)
Theory gasSummaryComposePtrAll
Ancestors
  fragGasMode
  gasSummaryComposePtr fragGasPathPtr gasStorage gasSummary gasExemptCert
  fragExec vyperStorageTrace vyperState vyperInterpreter

Theorem gas_outcome_ptr_bind_all:
  gas_outcome_ptr D tops (ctx, func) PG cx st0 source (es, s0, G0, tn0) P E /\
  (!H res ee G tn t. P H res ee G tn t ==> ISL res) /\
  (!H res ee gt r.
     valid_horizon cx st0 H ee.storage_trace /\ exit_result r /\
     E H res ee gt r ==>
     ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!v. storage_trace_frame (next v)) /\
  (!left v mid t G tn.
     gas_marked_exec F (ctx, func) source (es, s0) left (INL v) mid (OK t) /\
     (?H. valid_horizon cx st0 H mid.storage_trace) /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
          gas_path_ptr (D H) 0 ctx func PG G0 tn0 s0 (LENGTH left) G tn
            (OK t) /\
          P H (INL v) (mid with gas_obs := []) G tn t) ==>
     gas_outcome_ptr D tops (ctx, func) PG cx st0 (next v)
       (mid with gas_obs := [], t, G, tn) Q R) /\
  (!marks err ee leaf fstate.
     gas_exempt_cert F tops (ctx, func) (ignore_bind source (return ()))
       (es, s0) marks (err, ee) (leaf, fstate) ==>
     gas_exempt_cert F tops (ctx, func)
       (bind source (\v. ignore_bind (next v) (return ())))
       (es, s0) marks (err, ee) (leaf, fstate)) /\
  (!left v mid t right err ee leaf fstate.
     gas_marked_exec F (ctx, func) source (es, s0) left (INL v) mid (OK t) /\
     gas_exempt_cert F tops (ctx, func) (ignore_bind (next v) (return ()))
       (mid with gas_obs := [], t) right (err, ee) (leaf, fstate) ==>
     gas_exempt_cert F tops (ctx, func)
       (bind source (\v. ignore_bind (next v) (return ())))
       (es, s0) (left ++ right) (err, ee) (leaf, fstate)) ==>
  gas_outcome_ptr D tops (ctx, func) PG cx st0 (bind source next)
    (es, s0, G0, tn0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ source _ _ _`
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
      >- (qpat_x_assum `!H res ee G tn t. P H res ee G tn t ==> ISL res`
            (drule_then assume_tac) >>
          Cases_on `res` >> gvs[] >> rename1 `INL v` >>
          `gas_marked_exec F (ctx,func) source (es,s0) marks (INL v) es_end
             (OK t)` by (
            simp[gas_marked_exec_def, gas_marked_path_def] >>
            metis_tac[gas_path_ptr_erase]) >>
          mp_tac (Q.INST [`left` |-> `marks`, `mid` |-> `es_end`,
                          `G1` |-> `G`, `tn1` |-> `tn`]
                    gas_outcome_ptr_bind_normal) >>
          impl_tac >- (
            rpt conj_tac
            >- simp[]
            >- (gen_tac >> strip_tac >>
                qpat_x_assum
                  `!H. valid_horizon cx st0 H es_end.storage_trace ==> _`
                  (drule_then strip_assume_tac) >> simp[])
            >- simp[]
            >- (qpat_x_assum `!left v mid t G tn. _`
                  (qspecl_then [`marks`, `v`, `es_end`, `t`, `G`, `tn`]
                     mp_tac) >>
                impl_tac >- (
                  conj_tac >- simp[] >>
                  conj_tac >- (qexists_tac `H` >> simp[]) >>
                  gen_tac >> strip_tac >>
                  qpat_x_assum
                    `!H. valid_horizon cx st0 H es_end.storage_trace ==> _`
                    (drule_then strip_assume_tac) >>
                  gvs[exit_result_def]) >>
                simp[]) >>
            rpt strip_tac >>
            qpat_x_assum `!left v mid t right err ee leaf fstate. _`
              (qspecl_then [`marks`, `v`, `es_end`, `t`, `right`,
                            `err`, `ee`, `leaf`, `fstate`] mp_tac) >>
            simp[]) >>
          simp[]) >>
      `valid_horizon cx st0 H (es_end with gas_obs := []).storage_trace` by
        simp[] >>
      qpat_x_assum `!H res ee gt r. _ ==> ?exc. _`
        (fn th => assume_tac th >> drule_all_then strip_assume_tac th) >>
      gvs[] >>
      rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >>
      disj2_tac >> disj1_tac >>
      mp_tac (Q.INST [`fin` |-> `es_end`]
                gas_summary_ptr_at_bind_exception) >>
      impl_tac >- (
        simp[] >> gen_tac >> strip_tac >>
        `valid_horizon cx st0 H' (es_end with gas_obs := []).storage_trace` by
          simp[] >>
        qpat_x_assum `!H. valid_horizon cx st0 H es_end.storage_trace ==> _`
          (drule_then strip_assume_tac) >>
        gvs[exit_result_def] >>
        qpat_x_assum `!H res ee gt r. _ ==> ?exc. _`
          (drule_all_then strip_assume_tac) >> gvs[]) >>
      simp[]) >>
  `ignore_bind (bind source next) (return ()) =
     bind source (\v. ignore_bind (next v) (return ()))` by
    simp[ignore_bind_def, bind_assoc] >>
  asm_rewrite_tac[gas_outcome_ptr_def] >> metis_tac[]
QED
