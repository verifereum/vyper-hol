(* A piece of S1 (loweringRuntimeCorrect's lower_vyper_runtime_unit_correct). *)
Theory externalBodySourceOk
Ancestors
  stmtSimDefs list pair e2eDefs supportedProgram
  externalBodySupport externalEntryBound vyperTypeInvariants vyperTypeStmtSoundness
  vyperTypeEvalSoundness vyperTypeExprSoundness
  vyperInterpreter vyperState vyperContext evalNoHalt
  vyperTypeEvalProofs nonreentrantEquiv

val _ = Parse.hide "body";

Theorem external_body_source_ok_nr:
  !tops am tx ret os mut nr args dflts fbody gs0 es0 es_lock gs res es'.
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, nr, args, dflts, ret, fbody) /\
    external_entry_bound tops am tx os gs0 mut args dflts es0 /\
    lock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
      nr (is_view_mut mut) es0 = (INL (), es_lock) /\
    eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
      fbody (es_lock with gas_obs := gs) = (res, es') ==>
    stmt_res_ok NoLoop res /\ (res = INL () ==> ret = NoneT)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all external_lookup_body_typing >> strip_tac >>
  drule_all external_entry_bound_source_frame >> strip_tac >>
  drule_all external_selected_env_consistent >> strip_tac >>
  drule_all external_source_context_typed >> strip_tac >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx NONE` >>
  drule external_body_lock_frame >> strip_tac >>
  `state_well_typed (es_lock with gas_obs := gs)` by
    gvs[state_well_typed_def] >>
  `env_consistent env_t cx es_lock` by
    (qpat_assum `env_consistent _ _ es0` mp_tac >>
     qpat_assum `es_lock.scopes = es0.scopes` (fn th =>
       qpat_assum `es_lock.immutables = es0.immutables` (fn th' =>
         POP_ASSUM_LIST (K ALL_TAC) >>
         simp_tac (srw_ss()) [env_consistent_def, env_scopes_consistent_def,
           env_immutables_consistent_def, th, th'])) >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `no_type_error_eval (eval_stmts cx fbody (es_lock with gas_obs := gs))` by
    (irule eval_stmts_no_type_error >> simp[] >>
     qexistsl_tac [`env_t`,`env'`,`ret`] >> simp[]) >>
  gvs[no_type_error_eval_def] >>
  conj_tac
  >- (Cases_on `res` >> simp[stmt_res_ok_def] >>
      drule_all stmts_no_control_escape_eval_stmts_no_loop_control >>
      strip_tac >> Cases_on `y` >> gvs[stmt_res_ok_def]
      >~ [`Error e`]
      >- (Cases_on `e` >> gvs[stmt_res_ok_def, no_type_error_result_def])) >>
  strip_tac >> Cases_on `ret = NoneT` >> simp[] >>
  `stmts_no_fallthrough fbody` by simp[] >>
  drule (cj 2 no_fallthrough_eval_no_success) >> metis_tac[]
QED

Theorem external_body_source_ok:
  !tops am tx ret vs mut args fbody env es0 gs res es'.
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) /\
    eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
      fbody (es0 with gas_obs := gs) = (res, es') ==>
    stmt_res_ok NoLoop res /\ (res = INL () ==> ret = NoneT)
Proof
  rpt strip_tac >>
  drule_all external_entry_bound_no_defaults >>
  disch_then (qspec_then `es0.gas_obs` assume_tac) >>
  `es0 with gas_obs := es0.gas_obs = es0` by
    simp[evaluation_state_component_equality] >>
  qpat_x_assum `es0 with gas_obs := _ = es0` (fn th =>
    qpat_x_assum `external_entry_bound _ _ _ _ _ _ _ _ _`
      (assume_tac o REWRITE_RULE [th])) >>
  mp_tac (Q.SPECL [`tops`, `am`, `tx`, `ret`, `vs.vs_outcomes`, `mut`, `F`,
    `args`, `[]`, `fbody`, `es0.gas_obs`, `es0`, `es0`, `gs`, `res`, `es'`]
    external_body_source_ok_nr) >>
  simp[lock_if_nr_def, vyperStateTheory.return_def]
QED
