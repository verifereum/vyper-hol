(*
 * The selected external call at any gas observations: S1's
 * send_call_value_with_gas_obs and call_external_selected_body_gas, the
 * counted form of loweringRuntimeCorrect's call_external_selected_body.
 *
 * TOP-LEVEL:
 *   send_call_value_with_gas_obs -- moving the value ignores gas_obs
 *   call_external_selected_body_gas -- the selected call's result at gas
 *     observations gobs
 *)
Theory loweringPtrBodySource
Ancestors
  loweringRuntimeCorrect vyperTypeSelectedEntrySoundness vyperInterpreter
  vyperContext e2eDefs supportedProgram vyperLoweringCorrect venomState

val _ = Parse.hide "body";

Theorem send_call_value_with_gas_obs:
  !mut cx s r s'.
    send_call_value mut cx s = (r, s') ==>
    s'.gas_obs = s.gas_obs /\
    !gs. send_call_value mut cx (s with gas_obs := gs) =
         (r, s' with gas_obs := gs)
Proof
  rw[send_call_value_def, transfer_value_def, vyperStateTheory.bind_def,
     vyperStateTheory.ignore_bind_def, vyperStateTheory.check_def,
     vyperStateTheory.assert_def, vyperStateTheory.return_def,
     vyperStateTheory.raise_def, vyperStateTheory.get_accounts_def,
     vyperStateTheory.update_accounts_def] >>
  gvs[AllCaseEqs()]
QED

Theorem call_external_selected_body_gas:
  !tops am tx ret mut args fbody env orc gobs es0.
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    LENGTH tx.args = LENGTH args /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with <| outcomes := orc; requests := [] |>) =
      (INL (), es0) ==>
    call_external orc gobs am tx =
      case call_external_body am
             (initial_evaluation_context am.sources am.layouts tx NONE)
             F mut (type_env tops) (es0 with gas_obs := gobs) env fbody ret of
        (INL v, am', rqs) => (INL v, finalize_pending_deletions am', rqs)
      | failure => failure
Proof
  rw[source_deployment_rel_def] >>
  `type_env_all_modules [(NONE, tops)] = type_env tops` by
    simp[type_env_all_modules_def, type_env_def] >>
  simp[call_external_def, find_function_module_def,
       lookup_exported_function_def, get_self_code_def, get_module_code_def,
       initial_evaluation_context_def] >>
  qmatch_goalsub_abbrev_tac `call_external_function orc gobs am cx` >>
  qabbrev_tac `es1 = (es0 with gas_obs := gobs) with scopes := [FEMPTY]` >>
  `send_call_value mut cx
     (initial_state am [FEMPTY] with
        <| outcomes := orc; requests := []; gas_obs := gobs |>) =
   (INL (), es1)` by
    (qpat_x_assum `send_call_value _ _ _ = _` mp_tac >>
     simp[Abbr `cx`, initial_evaluation_context_def] >> strip_tac >>
     drule send_call_value_with_gas_obs >> strip_tac >>
     pop_assum (qspec_then `gobs` assume_tac) >>
     drule send_call_value_with_scopes >> strip_tac >>
     pop_assum (qspec_then `[FEMPTY]` mp_tac) >>
     simp[Abbr `es1`, initial_state_def]) >>
  `eval_external_defaults cx [] es1 = (INL [], es1)` by
    simp[Abbr `es1`, eval_external_defaults_def, evaluate_def,
         vyperStateTheory.bind_def,
         vyperStateTheory.ignore_bind_def, vyperStateTheory.get_scopes_def,
         vyperStateTheory.set_scopes_def, vyperStateTheory.finally_def,
         vyperStateTheory.return_def] >>
  `call_external_function orc gobs am cx F mut tops [(NONE, tops)] args []
     tx.args fbody ret =
   call_external_body am cx F mut (type_env tops) es1 env fbody ret` by
    (qpat_assum `_ = type_env tops` (SUBST1_TAC o SYM) >>
     irule call_external_function_body >> gvs[Abbr `cx`]) >>
  gvs[Abbr `es1`, call_external_body_def, vyperStateTheory.bind_def,
      vyperStateTheory.ignore_bind_def, vyperStateTheory.set_scopes_def]
QED
