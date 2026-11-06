(* Replay and counted-continuation boundaries for the selected external return. *)
Theory externalReturnCountedBoundary
Ancestors externalReturnSelectedSuffix stmtSimReturn stmtSimProps stmtSimDefs
  exprSimProps exprSimDefs loweringPosts exprSimHypsDefs
  gasOutcome gasSummary gasSummaryCompose gasContext gasCount fragGasPath fragGasMode
  gasExemptCert vyperInterpreter vyperState venomState

Theorem return_result_gas_obs:
  external_call_result_rel tops ret tx
    (INL v, finalize_pending_deletions
      (abstract_machine_from_state am.sources am.exports am.layouts
        (ee with gas_obs := gs)), (ee with gas_obs := gs).requests) r <=>
  external_call_result_rel tops ret tx
    (INL v, finalize_pending_deletions
      (abstract_machine_from_state am.sources am.exports am.layouts ee), ee.requests) r
Proof
  simp[abstract_machine_from_state_gas_obs]
QED

Theorem return_result_scopes:
  external_call_result_rel tops ret tx
    (INL v, finalize_pending_deletions
      (abstract_machine_from_state am.sources am.exports am.layouts
        (ee with scopes := sc)), (ee with scopes := sc).requests) r <=>
  external_call_result_rel tops ret tx
    (INL v, finalize_pending_deletions
      (abstract_machine_from_state am.sources am.exports am.layouts ee), ee.requests) r
Proof
  simp[abstract_machine_from_state_def]
QED

Theorem return_expr_post_start_gas_obs:
  expr_post ctx func ce cx e (es with gas_obs := gs) sa sb s0 ee v op s <=>
  expr_post ctx func ce cx e es sa sb s0 ee v op s
Proof
  simp[expr_post_def, locals_kept_def]
QED

Theorem return_counted_continuation:
  gas_outcome F tops (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee t. ?v. res = INL v /\ P v ee t)
    (\res ee r. expr_exit res r) /\
  (!marks ee v t.
    bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
        (INL v, ee) /\
    P v ee t /\ ~t.vs_halted ==>
    ?n r. gas_path ctx func t n r /\ exit_result r /\
      !tail. stmt_exit RetQ (ee with gas_obs := tail)
        (INR (ReturnException v)) r) ==>
  gas_outcome F tops (ctx,func) (eval_stmt cx (Return (SOME e))) (es,s0)
    Q (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  `eval_stmt cx (Return (SOME e)) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v. raise (ReturnException v))` by
    (simp[FUN_EQ_THM, eval_return_forced] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  simp[gas_outcome_def] >> strip_tac
  >- (
    qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
    simp[gas_summary_at_def] >> strip_tac
    >- (gvs[] >>
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
      first_x_assum drule_all >> strip_tac >>
      `gas_marked_exec F (ctx,func)
        (raise (ReturnException v) : evaluation_state -> unit evaluation_result)
        (es_end with gas_obs := [],t) (REPLICATE n F)
        (INR (ReturnException v)) es_end r` by
        (irule gas_marked_exec_no_source_read >>
         simp[raise_def, gas_marked_path_def, evaluation_state_component_equality]) >>
      qexists_tac `marks ++ REPLICATE n F` >> disj1_tac >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INR (ReturnException v)`, `es_end`, `r`] >>
      conj_tac
      >- (asm_rewrite_tac[] >>
          irule gas_marked_exec_bind_normal >>
          qexistsl_tac [`es_end`, `t`, `v`] >> simp[]) >>
      disj2_tac >>
      `!tail. (es_end with gas_obs := []) with gas_obs := tail =
        es_end with gas_obs := tail` by
        simp[evaluation_state_component_equality] >>
      gvs[]) >>
    `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
    qexists_tac `marks` >> disj1_tac >> simp[gas_summary_at_def] >>
    qexistsl_tac [`INR ex`, `es_end`, `r`] >> conj_tac
    >- (asm_rewrite_tac[] >>
        irule gas_marked_exec_bind_exception >> simp[]) >>
    simp[] >> disj2_tac >> gen_tac >> simp[stmt_exit_def] >> disj1_tac >>
    metis_tac[expr_exit_INR_type]) >>
  qexists_tac `marks` >> disj2_tac >>
  metis_tac[return_forced_exempt]
QED
