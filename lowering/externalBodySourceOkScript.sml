(* A piece of S1 (loweringRuntimeCorrect's lower_vyper_runtime_unit_correct). *)
Theory externalBodySourceOk
Ancestors
  stmtSimProps
  stmtSimDefs
  exprSimDefs
  loweringPosts
  list pair fragExec  bodySim bodySimMain loweringHalt stmtLoweringMono  exprLoweringProps
  compileEnv compileVyper moduleLowering stmtLowering
  e2eDefs supportedProgram vyperLoweringCorrect rawReturnHeader
  vyperTypeSelectedEntrySoundness vyperTypeSystem
  externalBodySupport vyperTypeInvariants vyperTypeStmtSoundness
  vyperTypeEvalSoundness vyperTypeExprSoundness
  vyperInterpreter vyperState vyperContext
  venomState venomExecSemantics venomWf

val _ = Parse.hide "body";

Theorem external_body_source_ok:
  !tops am tx ret vs mut args fbody env es0 gs res es'.
    supported_program tops /\ source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\ source_deployment_rel tops am tx /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
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
  rpt gen_tac >> strip_tac >>
  drule_all external_selected_body_typing >> strip_tac >>
  `machine_well_typed am` by gvs[source_typing_ok_def] >>
  drule_all external_body_prefix_state >> strip_tac >>
  drule_all external_selected_env_consistent >> strip_tac >>
  drule external_source_context_typed >> strip_tac >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx NONE` >>
  `no_type_error_eval (eval_stmts cx fbody (es0 with gas_obs := gs))` by
    (irule eval_stmts_no_type_error >> simp[] >> metis_tac[]) >>
  gvs[no_type_error_eval_def] >>
  conj_tac
  >- (Cases_on `res` >> simp[stmt_res_ok_def] >>
      drule_all stmts_no_control_escape_eval_stmts_no_loop_control >>
      strip_tac >> Cases_on `y` >> gvs[stmt_res_ok_def] >>
      rename1 `Error e` >> Cases_on `e` >>
      gvs[stmt_res_ok_def, no_type_error_result_def]) >>
  strip_tac >> Cases_on `ret = NoneT` >> simp[] >>
  `stmts_no_fallthrough fbody` by simp[] >>
  drule (cj 2 no_fallthrough_eval_no_success) >> metis_tac[]
QED

