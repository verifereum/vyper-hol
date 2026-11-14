(* Assign-specific RHS outcome boundary for a top-level target. *)
Theory bodyFullAssignToplevelSource
Ancestors
  gasOutcomeFull gasOutcomeFullCompose gasExemptCert gasStorage
  gasContext stmtSimDefs
  vyperStorageTrace vyperStorageFootprint vyperState vyperInterpreter
  venomState fragExec fragGasOriginPtr list

Theorem body_assign_toplevel_word_full_source:
  gasContext$gas_admissible (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
    (stmtSimDefs$stmt_res_ok lctx) es /\
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
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (es,s,G,tn) Q R) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
    (es,s,G,tn) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def])
  >- (rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
      disj1_tac >> conj_tac
      >- (pure_once_rewrite_tac[Once evaluate_def] >>
          pure_rewrite_tac[GSYM bind_assoc] >>
          irule gas_bad_storage_at_bind_left >> simp[] >> gen_tac >>
          irule storage_trace_frame_bind_all >>
          simp[evaluate_storage_trace_frame,storage_trace_frame_write_place]) >>
      metis_tac[])
  >- suspend "normal"
  >> rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks` >>
     disj2_tac >> disj2_tac >>
     qexistsl [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
     conj_tac
     >- (simp[Once evaluate_def,ignore_bind_def,GSYM bind_assoc] >>
         pure_once_rewrite_tac[bind_assoc] >>
         CONV_TAC (DEPTH_CONV ETA_CONV) >>
         irule gas_exempt_cert_error_value >> simp[ignore_bind_def]) >>
     metis_tac[]
QED

Resume body_assign_toplevel_word_full_source[normal]:
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  Cases_on `?t. r = OK t`
  >- (gvs[] >> first_x_assum irule >>
      qexistsl [`G'`,`marks`,`ee`,`res`,`t`,`tn'`] >>
      gvs[exit_result_def]) >>
  `?exc. res = INR exc` by metis_tac[] >> gvs[] >>
  irule gas_outcome_full_intro >>
  qexistsl [`G'`,`ee`,`marks`,`r`,`INR exc`,`tn'`] >>
  conj_tac
  >- (gen_tac >> pure_once_rewrite_tac[Once evaluate_def] >>
      pure_rewrite_tac[GSYM bind_assoc] >> CONV_TAC (DEPTH_CONV ETA_CONV) >>
      simp[Once bind_def]) >>
  simp[] >> metis_tac[]
QED

Finalise body_assign_toplevel_word_full_source
