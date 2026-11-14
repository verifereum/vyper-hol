(* Local Assign composition keeps the RHS exemption provenance. *)
Theory bodyFullAssignLocalSource
Ancestors
  gasOutcomeFull gasOutcomeFullCompose stmtSimAssignSource gasExemptCert
  gasStorage vyperStorageTrace vyperStorageFootprint vyperState
  vyperInterpreter venomState fragExec

Theorem body_assign_local_word_full_source:
  gas_admissible (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (stmt_res_ok lctx) es /\
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) Q1
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!marks res mid G1 tn1 t.
    (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (res, mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) marks (OK t,G1,tn1) /\
      Q1 H res (mid with gas_obs := []) G1 tn1 t) ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
      (es,s,G,tn) Q R) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e))
    (es,s,G,tn) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def])
  >- (rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
      disj1_tac >> conj_tac
      >- (drule assign_local_admissible_run >>
          disch_then (fn th => PURE_REWRITE_TAC [gas_bad_storage_at_def, th]) >>
          pure_rewrite_tac[GSYM gas_bad_storage_at_def] >>
          irule gas_bad_storage_at_bind_left >>
          simp[storage_trace_frame_write_place]) >> metis_tac[])
  >- suspend "normal"
  >> rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
     disj2_tac >> disj2_tac >>
     qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
     conj_tac >- (irule assign_local_exempt >>
       simp[gas_exempt_cert_unforce_result]) >> metis_tac[]
QED

Resume body_assign_local_word_full_source[normal]:
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  Cases_on `?t. r = OK t`
  >- (gvs[] >> first_x_assum irule >>
      qexistsl_tac [`G'`,`marks`,`ee`,`res`,`t`,`tn'`] >>
      gvs[exit_result_def]) >>
  `?exc. res = INR exc` by metis_tac[] >> gvs[] >>
  irule gas_outcome_full_intro >>
  qexistsl_tac [`G'`,`ee`,`marks`,`r`,`INR exc`,`tn'`] >>
  conj_tac
  >- (drule assign_local_admissible_run >> strip_tac >>
      simp[Once bind_def]) >> simp[] >> metis_tac[]
QED

Finalise body_assign_local_word_full_source
