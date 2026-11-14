Theory assignPlaceGasCompose
Ancestors
  exprSimSubscriptMap vyperInterpreter vyperState
  gasOutcome gasContext gasSummary gasSummaryCompose gasExemptCert

(* Preserve the RHS result and its marked replay until read_result has
   executed.  In particular the RHS need not be a Value constructor. *)
Theorem assign_place_result_outcome:
  gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0) P Exit /\
  (!res ee t. P res ee t ==> ?pv. res = INL pv) /\
  (!res ee r. Exit res ee r ==> ?ex. res = INR ex /\ R (INR ex) ee r) /\
  (!marks pv mid t.
     gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0)
       marks (INL pv) mid (OK t) /\
     P (INL pv) (mid with gas_obs := []) t ==>
     gas_outcome F (cx_tops cx) (ctx,func)
       (bind (read_result cx pv)
         (\v. bind (eval_target_place cx bt) (\p. write_place cx p v)))
       (mid with gas_obs := [],t) Q R) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_stmt cx (Assign (BaseTarget bt) e)) (es,s0) Q R
Proof
  strip_tac >>
  simp[Once evaluate_def] >>
  irule gas_outcome_bind_result_exec >>
  qexistsl_tac [`Exit`, `P`] >> simp[] >> metis_tac[]
QED

Theorem assign_place_target_outcome:
  gas_outcome memory tops (ctx,func)
    (eval_target_place cx bt) (es,s0) Qa Ra /\
  (!marks res mid t.
    gas_marked_exec memory (ctx,func) (eval_target_place cx bt)
      (es,s0) marks res mid (OK t) /\
    Qa res (mid with gas_obs := []) t ==>
    ?p. res = INL p /\
      gas_outcome memory tops (ctx,func) (write_place cx p v)
        (mid with gas_obs := [],t) Q R) /\
  (!res ee r. exit_result r /\ Ra res ee r ==>
    ?ex. res = INR ex /\ R (INR ex) ee r) ==>
  gas_outcome memory tops (ctx,func)
    (bind (eval_target_place cx bt) (\p. write_place cx p v)) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ (eval_target_place _ _) _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `left` strip_assume_tac)
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- (rpt BasicProvers.VAR_EQ_TAC >>
          first_x_assum drule_all >> strip_tac >>
          rpt BasicProvers.VAR_EQ_TAC >>
          qpat_x_assum `gas_outcome _ _ _ (write_place _ _ _) _ _ _` mp_tac >>
          rewrite_tac[gas_outcome_def] >>
          disch_then (qx_choose_then `right` strip_assume_tac)
          >- (qexists_tac `left ++ right` >> disj1_tac >>
              qpat_x_assum `gas_summary_at _ _ _ (write_place _ _ _) _ _ _`
                (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
              rewrite_tac[gas_summary_at_def] >>
              rename1 `gas_marked_exec _ _ (write_place cx p v) _ right rr fin rq` >>
              qexistsl_tac [`rr`, `fin`, `rq`] >>
              (conj_tac
               >- (irule gas_marked_exec_bind_normal >>
                   qexistsl_tac [`es_end`, `t`, `p`] >> gvs[]) >> simp[])) >>
          qexists_tac `left ++ right` >> disj2_tac >>
          rename1 `gas_exempt_cert _ _ _ _ _ _ (err,ee) (leaf,target)` >>
          qexistsl_tac [`err`, `ee`, `leaf`, `target`] >>
          simp[ignore_bind_def, bind_assoc] >>
          irule gas_exempt_cert_bind_place >>
          qexistsl_tac [`es_end`, `t`, `p`] >> simp[GSYM ignore_bind_def]) >>
      first_x_assum drule_all >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      qexists_tac `left` >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR ex`, `es_end`, `r`] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >> simp[]) >>
  qexists_tac `left` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_place >> simp[GSYM ignore_bind_def]
QED
