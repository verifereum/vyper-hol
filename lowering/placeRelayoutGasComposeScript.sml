(* Counted composition across the place-valued target action. *)
Theory placeRelayoutGasCompose
Ancestors
  placeRelayoutGasSource gasOutcome gasSummary gasSummaryCompose gasExemptCert
  exprSimSubscriptMap stmtSimDefs exprSimDefs vyperState vyperInterpreter

Theorem gas_outcome_bind_place:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> place evaluation_result) (es,s0) Qa Ra /\
  (!marks res mid t.
    gas_marked_exec memory (ctx,func) a (es,s0) marks res mid (OK t) /\
    Qa res (mid with gas_obs := []) t ==>
    ?v. res = INL v /\
      gas_outcome memory tops (ctx,func) (k v) (mid with gas_obs := [],t) Q R) /\
  (!res ee r. exit_result r /\ Ra res ee r ==>
    ?ex. res = INR ex /\ R (INR ex) ee r) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ a _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `left` strip_assume_tac)
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- (rpt BasicProvers.VAR_EQ_TAC >>
          first_x_assum drule_all >> strip_tac >>
          rpt BasicProvers.VAR_EQ_TAC >>
          qpat_x_assum `gas_outcome _ _ _ (k _) _ _ _` mp_tac >>
          rewrite_tac[gas_outcome_def] >>
          disch_then (qx_choose_then `right` strip_assume_tac)
          >- (qexists_tac `left ++ right` >> disj1_tac >>
              qpat_x_assum `gas_summary_at _ _ _ (k _) _ _ _`
                (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
              rewrite_tac[gas_summary_at_def] >>
              rename1 `gas_marked_exec _ _ (k v) _ right rr fin rq` >>
              qexistsl_tac [`rr`, `fin`, `rq`] >>
              (conj_tac
               >- (irule gas_marked_exec_bind_normal >>
                   qexistsl_tac [`es_end`, `t`, `v`] >> simp[]) >> simp[])) >>
          qexists_tac `left ++ right` >> disj2_tac >>
          rename1 `gas_exempt_cert _ _ _ _ _ _ (err,ee) (leaf,target)` >>
          qexistsl_tac [`err`, `ee`, `leaf`, `target`] >>
          simp[ignore_bind_def, bind_assoc] >>
          irule gas_exempt_cert_bind_place >>
          qexistsl_tac [`es_end`, `t`, `v`] >> simp[GSYM ignore_bind_def]) >>
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

(* The RHS is read only after the target.  Concrete Value results make that
   read a no-op, without commuting it past any effectful source action. *)
Theorem assign_place_raw_outcome:
  gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0) Qa Ra /\
  (!res ee t. Qa res ee t ==> ?v. res = INL (Value v)) /\
  (!res ee r. Ra res ee r ==> ?ex. res = INR ex /\ R (INR ex) ee r) /\
  (!marks v mid t.
    gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0)
      marks (INL (Value v)) mid (OK t) /\
    Qa (INL (Value v)) (mid with gas_obs := []) t ==>
    gas_outcome F (cx_tops cx) (ctx,func)
      (bind (eval_target_place cx bt) (\p. write_place cx p v))
      (mid with gas_obs := [],t) Q R) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_stmt cx (Assign (BaseTarget bt) e)) (es,s0) Q R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[Once evaluate_def] >>
  irule gas_outcome_bind_result_exec >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> rename1 `Qa (INL pv) _ _` >>
      `?v. pv = Value v` by metis_tac[sumTheory.INL_11] >> gvs[] >>
      simp[read_result_def, bind_return] >>
      first_x_assum irule >> metis_tac[]) >>
  metis_tac[]
QED
