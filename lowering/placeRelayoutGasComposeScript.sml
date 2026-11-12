(* Counted composition across the place-valued target action. *)
Theory placeRelayoutGasCompose
Ancestors
  placeRelayoutGasSource gasOutcome gasSummary gasSummaryCompose gasExemptCert
  exprSimSubscriptMap stmtSimDefs exprSimDefs vyperState vyperInterpreter
  gasStorage vyperStorageFootprint vyperStorageTrace

Theorem gas_outcome_bind_place:
  gas_outcome memory tops (ctx,func) cx st0
    (a : evaluation_state -> place evaluation_result) (es,s0) Qa Ra /\
  (!marks res mid t.
    gas_marked_exec memory (ctx,func) a (es,s0) marks res mid (OK t) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       Qa H res (mid with gas_obs := []) t) ==>
    ?v. res = INL v /\
      gas_outcome memory tops (ctx,func) cx st0 (k v)
        (mid with gas_obs := [],t) Q R) /\
  (!H res ee r. exit_result r /\ Ra H res ee r ==>
    ?ex. res = INR ex /\ R H (INR ex) ee r) /\
  (!v. storage_trace_frame (k v)) ==>
  gas_outcome memory tops (ctx,func) cx st0 (bind a k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ a _ _ _`
    (mp_tac o BETA_RULE o REWRITE_RULE [gas_outcome_def]) >>
  disch_then (qx_choose_then `left` (DISJ_CASES_THEN mp_tac))
  >- (strip_tac >> rewrite_tac[gas_outcome_def] >>
      qexists_tac `left` >> disj1_tac >>
      irule gas_bad_storage_at_bind_left >> simp[]) >>
  disch_then (DISJ_CASES_THEN mp_tac)
  >- (rewrite_tac[gas_summary_at_def] >> BETA_TAC >>
      disch_then (qx_choose_then `res` (qx_choose_then `mid`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
      reverse (Cases_on `storage_trace_domain cx st0 mid.storage_trace`)
      >- (disch_then kall_tac >> rewrite_tac[gas_outcome_def] >>
          qexists_tac `left` >> disj1_tac >>
          irule gas_bad_storage_at_bind_left >> simp[] >>
          irule gas_bad_storage_at_counted_prefix >>
          metis_tac[]) >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
         mid.storage_trace` by fs[storage_trace_domain_def] >>
      disch_then (DISJ_CASES_THEN strip_assume_tac)
      >- (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
            (assume_tac o SIMP_RULE (srw_ss()) []) >>
          rpt BasicProvers.VAR_EQ_TAC >>
          qpat_x_assum `!marks res mid t. _`
            (qspecl_then [`left`, `res`, `mid`, `t`] mp_tac) >>
          impl_tac >- simp[] >> strip_tac >>
          rpt BasicProvers.VAR_EQ_TAC >>
          qpat_x_assum `gas_outcome _ _ _ _ _ (k _) _ _ _` mp_tac >>
          rewrite_tac[gas_outcome_def] >>
          disch_then (qx_choose_then `right` (DISJ_CASES_THEN mp_tac))
          >- (strip_tac >> qexists_tac `left ++ right` >> disj1_tac >>
              irule gas_bad_storage_at_bind_right >> metis_tac[]) >>
          disch_then (DISJ_CASES_THEN mp_tac)
          >- (rewrite_tac[gas_summary_at_def] >>
              disch_then (qx_choose_then `out` (qx_choose_then `fin`
                (qx_choose_then `rr` (CONJUNCTS_THEN2 assume_tac assume_tac)))) >>
              qexists_tac `left ++ right` >> disj2_tac >> disj1_tac >>
              rewrite_tac[gas_summary_at_def] >>
              qexistsl_tac [`out`, `fin`, `rr`] >>
              conj_tac >- (irule gas_marked_exec_bind_normal >>
                           goal_assum drule >> simp[]) >>
              first_assum ACCEPT_TAC) >>
          strip_tac >>
          rename1 `gas_exempt_cert _ _ _ _ _ right (err, ef) (callee, tf)` >>
          qexists_tac `left ++ right` >> disj2_tac >> disj2_tac >>
          qexistsl_tac [`err`, `ef`, `callee`, `tf`] >>
          rewrite_tac[ignore_bind_def, bind_assoc] >>
          irule gas_exempt_cert_bind_place >>
          qexistsl_tac [`mid`, `t`, `v`] >> simp[GSYM ignore_bind_def]) >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
        (assume_tac o SIMP_RULE (srw_ss()) []) >>
      `?ex. res = INR ex` by metis_tac[] >> gvs[] >>
      rewrite_tac[gas_outcome_def] >>
      qexists_tac `left` >> disj2_tac >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >>
      qexistsl_tac [`INR ex`, `mid`, `r`] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      BETA_TAC >> simp[] >> rpt strip_tac >>
      `?ex'. INR ex = INR ex' /\ R H (INR ex') (mid with gas_obs := []) r` by
        metis_tac[] >>
      gvs[]) >>
  strip_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ left (err, ef) (callee, tf)` >>
  rewrite_tac[gas_outcome_def] >>
  qexists_tac `left` >> disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`, `ef`, `callee`, `tf`] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_place >> simp[]
QED

(* The RHS is read only after the target.  Concrete Value results make that
   read a no-op, without commuting it past any effectful source action. *)
Theorem assign_place_raw_outcome:
  gas_outcome F (cx_tops cx) (ctx,func) cx st0 (eval_expr cx e) (es,s0) Qa Ra /\
  (!H res ee t. Qa H res ee t ==> ?v. res = INL (Value v)) /\
  (!H res ee r. Ra H res ee r ==> ?ex. res = INR ex /\ R H (INR ex) ee r) /\
  (!marks v mid t.
    gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s0)
      marks (INL (Value v)) mid (OK t) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       Qa H (INL (Value v)) (mid with gas_obs := []) t) ==>
    gas_outcome F (cx_tops cx) (ctx,func) cx st0
      (bind (eval_target_place cx bt) (\p. write_place cx p v))
      (mid with gas_obs := [],t) Q R) ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (eval_stmt cx (Assign (BaseTarget bt) e)) (es,s0) Q R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[Once evaluate_def] >>
  irule gas_outcome_bind_result_exec >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _ _ _`)) >>
  rpt conj_tac
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_read_result] >> gen_tac >>
      irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_write_place])
  >~ [`gas_outcome _ _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> rename1 `gas_marked_exec _ _ _ _ _ (INL pv) _ _` >>
      reverse (Cases_on `storage_trace_domain cx st0 mid.storage_trace`)
      >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
          irule gas_bad_storage_at_initial >> simp[] >>
          irule storage_trace_frame_bind_all >>
          simp[storage_trace_frame_read_result] >> gen_tac >>
          irule storage_trace_frame_bind_all >>
          simp[evaluate_storage_trace_frame, storage_trace_frame_write_place]) >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
         mid.storage_trace` by fs[storage_trace_domain_def] >>
      `?v. pv = Value v` by metis_tac[sumTheory.INL_11] >> gvs[] >>
      simp[read_result_def, bind_return] >>
      qpat_x_assum `!marks v mid t. _` irule >> metis_tac[]) >>
  metis_tac[]
QED
