(* Checked default expressions leave the storage trace unchanged. The
   initializer's normal or exceptional endpoint therefore has a horizon. *)
Theory groupedDefaultOutcome
Ancestors
  createSizeExit gasOutcomeFull gasStorage gasExemptCert gasSummary groupedDefaultHorizon
  vyperStorageFootprint vyperInterpreter vyperState vyperEvalReadingErrors fragExec list

Theorem grouped_default_initializer_outcome:
  storage_trace_domain cx st0 es.storage_trace /\
  (!gs. (SND (eval_exprs cx ds (es with gas_obs := gs))).storage_trace =
      es.storage_trace) /\
  gas_outcome_full (DF,lo,explicit,ctx,fn,PG) tops cx st0
    (eval_exprs cx ds) (es,s,G,tn) Q R ==>
  ?marks res ee.
    (!tail. eval_exprs cx ds
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (res,ee with gas_obs := tail)) /\
    ee.storage_trace = es.storage_trace /\
    ((?r J u.
      !H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) marks (r,J,u) /\
        ((?t. r = OK t /\ Q H res (ee with gas_obs := []) J u t) \/
         (exit_result r /\ create_size_exit_ok ctx res r /\
          R H res (ee with gas_obs := []) (J,u) r))) \/
     (?err H leaf leaf_pg leaf_g leaf_tn finish.
       res = INR (Error err) /\ unspecified_behaviour_exempt tops err /\
       valid_horizon cx st0 H es.storage_trace /\
       gas_origin_ptr_focus (DF H,lo,explicit,ctx,fn,PG) (s,G,tn) marks
         (leaf,leaf_pg,leaf_g,leaf_tn,finish)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (qx_choose_then `marks` strip_assume_tac o REWRITE_RULE [gas_outcome_full_def])
  >- (qpat_x_assum `gas_bad_storage_at _ _ _ _ _ _`
        (qspec_then `[]:bytes32 list` mp_tac o REWRITE_RULE [gas_bad_storage_at_def]) >>
      simp[])
  >- (qexistsl_tac [`marks`,`res`,`ee`] >>
      `ee.storage_trace = es.storage_trace` by
        (qpat_assum `!gs. (SND _).storage_trace = _`
           (qspec_then `gas_explicit marks s.vs_gas_readings` mp_tac) >>
         qpat_assum `!tail. eval_exprs _ _ _ = _`
           (qspec_then `[]:bytes32 list`
             (fn th => PURE_REWRITE_TAC [REWRITE_RULE [APPEND_NIL] th])) >>
         simp[evaluation_state_accfupds]) >>
      asm_rewrite_tac[] >> disj1_tac >> qexistsl_tac [`r`,`G'`,`tn'`] >>
      qpat_assum `ee.storage_trace = es.storage_trace` (fn th => pure_rewrite_tac [SYM th]) >>
      first_assum ACCEPT_TAC) >>
  qmatch_asmsub_rename_tac `gas_origin_ptr_focus _ _ _ (leaf,leaf_pg,leaf_g,leaf_tn,target)` >>
  drule gas_exempt_cert_execution >> strip_tac >>
  `!tail. eval_exprs cx ds
    (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
    (INR (Error err),ee with gas_obs := tail)` by
    (gen_tac >>
     qpat_assum `!tail. ignore_bind _ _ _ = _` (qspec_then `tail` mp_tac) >>
     Cases_on `eval_exprs cx ds
       (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail)` >>
     Cases_on `q` >> gvs[ignore_bind_def,bind_def,return_def]) >>
  qexistsl_tac [`marks`,`INR (Error err)`,`ee`] >>
  `ee.storage_trace = es.storage_trace` by
    (qpat_assum `!gs. (SND _).storage_trace = _`
       (qspec_then `gas_explicit marks s.vs_gas_readings` mp_tac) >>
     qpat_assum `!tail. eval_exprs _ _ _ = _`
       (qspec_then `[]:bytes32 list`
             (fn th => PURE_REWRITE_TAC [REWRITE_RULE [APPEND_NIL] th])) >>
         simp[evaluation_state_accfupds]) >>
  asm_rewrite_tac[] >> disj2_tac >>
  qexistsl_tac [`err`,`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`target`] >>
  fs[]
QED

Theorem grouped_default_readings_not_missing:
  (!tail. eval_exprs cx ds (es with gas_obs := readings ++ tail) =
    (res,ee with gas_obs := tail)) ==>
  res <> INR (Error (RuntimeError "msg.gas: no gas reading"))
Proof
  strip_tac >> strip_tac >>
  first_x_assum (qspec_then `[ARB:bytes32]` assume_tac) >>
  qpat_x_assum `res = _` SUBST_ALL_TAC >>
  drule (cj 6 evaluate_missing_reading_state) >> simp[]
QED
