(* Replay and counted-continuation boundaries for the selected external return. *)
Theory externalReturnCountedBoundary
Ancestors externalReturnSelectedSuffix stmtSimReturn stmtSimProps stmtSimDefs
  exprSimProps exprSimDefs loweringPosts exprSimHypsDefs
  gasOutcome gasSummary gasSummaryCompose gasContext gasCount fragGasPath fragGasMode
  gasExemptCert gasStorage vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperState venomState

Theorem return_result_gas_obs:
  external_call_result_rel H tops ret tx
    (INL v, finalize_pending_deletions
      (abstract_machine_from_state am.sources am.exports am.layouts
        (ee with gas_obs := gs)), (ee with gas_obs := gs).requests) r <=>
  external_call_result_rel H tops ret tx
    (INL v, finalize_pending_deletions
      (abstract_machine_from_state am.sources am.exports am.layouts ee), ee.requests) r
Proof
  simp[abstract_machine_from_state_gas_obs]
QED

Theorem return_result_scopes:
  external_call_result_rel H tops ret tx
    (INL v, finalize_pending_deletions
      (abstract_machine_from_state am.sources am.exports am.layouts
        (ee with scopes := sc)), (ee with scopes := sc).requests) r <=>
  external_call_result_rel H tops ret tx
    (INL v, finalize_pending_deletions
      (abstract_machine_from_state am.sources am.exports am.layouts ee), ee.requests) r
Proof
  simp[abstract_machine_from_state_def]
QED

Theorem return_expr_post_start_gas_obs:
  expr_post H ctx func ce cx e (es with gas_obs := gs) sa sb s0 ee v op s <=>
  expr_post H ctx func ce cx e es sa sb s0 ee v op s
Proof
  simp[expr_post_def, locals_kept_def, popped_kept_def]
QED

Theorem return_counted_continuation:
  gas_outcome F tops (ctx,func) cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\H res ee t. ?v. res = INL v /\ P H v ee t)
    (\H res ee r. expr_exit res r) /\
  (!marks ee v t H0.
    bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
        (INL v, ee) /\
    valid_horizon cx st0 H0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==> P H v ee t) /\
    ~t.vs_halted ==>
    ?n r. gas_path ctx func t n r /\ exit_result r /\
      !H. valid_horizon cx st0 H ee.storage_trace ==>
        !tail. stmt_exit (RetQ H) (ee with gas_obs := tail)
          (INR (ReturnException v)) r) ==>
  gas_outcome F tops (ctx,func) cx st0 (eval_stmt cx (Return (SOME e))) (es,s0)
    Q (\H res ee r. !tail. stmt_exit (RetQ H) (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  `eval_stmt cx (Return (SOME e)) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. raise (ReturnException v))` by
    (simp[FUN_EQ_THM, eval_return_forced] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >> BETA_TAC >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN mp_tac))
  >- (strip_tac >> qexists_tac `marks` >> disj1_tac >>
      irule gas_bad_storage_at_bind_left >>
      simp[storage_trace_frame_raise]) >>
  disch_then (DISJ_CASES_THEN mp_tac)
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `res` (qx_choose_then `es_end`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
      reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
      >- (disch_then kall_tac >> qexists_tac `marks` >> disj1_tac >>
          irule gas_bad_storage_at_bind_left >>
          simp[storage_trace_frame_raise] >>
          irule gas_bad_storage_at_counted_prefix >> metis_tac[]) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by fs[storage_trace_domain_def] >>
      disch_then (DISJ_CASES_THEN (strip_assume_tac o BETA_RULE))
      >- (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
            (assume_tac o SIMP_RULE (srw_ss()) []) >>
          first_assum (drule_then strip_assume_tac) >> gvs[] >>
          `~t.vs_halted` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
             simp[gas_marked_exec_def] >>
             metis_tac[gas_marked_path_exec, gas_path_normal]) >>
          `bind (eval_expr cx e) (read_result cx)
            (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
              (INL v, es_end with gas_obs := [])` by
            (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
             simp[gas_marked_exec_def] >>
             strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
          qpat_x_assum `!m ee v t H0. bind _ _ _ = _ /\ _ ==> _`
            (qspecl_then [`marks`, `es_end with gas_obs := []`, `v`, `t`,
               `storage_trace_horizon es_end.storage_trace`] mp_tac) >>
          impl_tac >- simp[] >>
          disch_then (qx_choosel_then [`n`, `rx`] strip_assume_tac) >>
          `gas_marked_exec F (ctx,func)
            (raise (ReturnException v) : evaluation_state -> unit evaluation_result)
            (es_end with gas_obs := [],t) (REPLICATE n F)
            (INR (ReturnException v)) es_end rx` by
            (irule gas_marked_exec_no_source_read >>
             simp[raise_def, gas_marked_path_def,
                  evaluation_state_component_equality]) >>
          qexists_tac `marks ++ REPLICATE n F` >> disj2_tac >> disj1_tac >>
          simp[gas_summary_at_def] >>
          qexistsl_tac [`INR (ReturnException v)`, `es_end`, `rx`] >>
          conj_tac
          >- (irule gas_marked_exec_bind_normal >>
              qexistsl_tac [`es_end`, `t`, `v`] >> simp[]) >>
          disj2_tac >>
          `!tail. (es_end with gas_obs := []) with gas_obs := tail =
            es_end with gas_obs := tail` by
            simp[evaluation_state_component_equality] >>
          gvs[]) >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
        (assume_tac o SIMP_RULE (srw_ss()) []) >>
      `expr_exit res r` by metis_tac[] >>
      `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
      qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INR ex`, `es_end`, `r`] >> conj_tac
      >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      disj2_tac >> simp[stmt_exit_def] >> rpt strip_tac >> disj1_tac >>
      metis_tac[expr_exit_INR_type]) >>
  strip_tac >> qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  drule return_forced_exempt >>
  `eval_stmt cx (Return (SOME e)) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. raise (ReturnException v))` by
    (simp[FUN_EQ_THM, eval_return_forced] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  pop_assum SUBST1_TAC >> metis_tac[]
QED
