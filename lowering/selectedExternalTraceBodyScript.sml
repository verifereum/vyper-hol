Theory selectedExternalTraceBody
Ancestors
  vyperInterpreter vyperState vyperContext vyperTypeSystem
  vyperTypeSelectedEntrySoundness
  e2eDefs externalCallSelected vyperCall

val _ = Parse.hide "body";

(* The source wrapper's complete result, including halt, with no defaults
   or nonreentrant lock.  No trace-extraction admission is used. *)
Theorem selected_external_trace_body_result:
  !tops am tx ret mut args fbody env orc gx es0 res ee.
    source_deployment_rel tops am tx /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := orc; requests := [] |>) = (INL (), es0) /\
    eval_stmts (initial_evaluation_context am.sources am.layouts tx NONE)
      fbody (es0 with gas_obs := gx) = (res, ee) ==>
    call_external_trace orc gx am tx =
      case res of
        INL () =>
          (INL NoneV, finalize_pending_deletions
            (abstract_machine_from_state am.sources am.exports am.layouts ee),
           ee.requests, ee.storage_trace)
      | INR (ReturnException v) =>
          (case evaluate_type (type_env tops) ret of
             NONE => (INR (Error (TypeError "eval ret")), am,
                      ee.requests, ee.storage_trace)
           | SOME tv =>
               case safe_cast tv v of
                 NONE => (INR (Error (TypeError "ext cast ret")), am,
                          ee.requests, ee.storage_trace)
               | SOME v' =>
                   (INL v', finalize_pending_deletions
                     (abstract_machine_from_state am.sources am.exports
                        am.layouts ee), ee.requests, ee.storage_trace))
      | INR HaltException =>
          (INR HaltException, finalize_pending_deletions
            (abstract_machine_from_state am.sources am.exports am.layouts ee),
           ee.requests, ee.storage_trace)
      | INR e => (INR e, am, ee.requests, ee.storage_trace)
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH tx.args = LENGTH args` by
    (drule bind_arguments_length >> simp[]) >>
  `es0.scopes = [env]` by
    (drule send_call_value_with_scopes >> simp[initial_state_def]) >>
  `es0 with scopes := [env] = es0` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  drule send_call_value_with_gas_obs >> strip_tac >>
  qpat_x_assum `!gs. send_call_value _ _ _ = _`
    (qspec_then `gx` assume_tac) >>
  drule send_call_value_with_scopes >> strip_tac >>
  qpat_x_assum `!sc. send_call_value _ _ _ = _`
    (qspec_then `[FEMPTY]` assume_tac) >>
  gvs[source_deployment_rel_def] >>
  `type_env_all_modules [(NONE, tops)] = type_env tops` by
    simp[type_env_all_modules_def, type_env_def] >>
  simp[call_external_trace_def, find_function_module_def,
       lookup_exported_function_def, get_self_code_def, get_module_code_def,
       initial_evaluation_context_def] >>
  gvs[initial_evaluation_context_def, initial_state_def] >>
  simp[call_external_function_trace_def, initial_evaluation_context_def,
       lock_if_nr_def, unlock_if_nr_def,
       vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.return_def, vyperStateTheory.set_scopes_def,
       initial_state_def] >>
  `es0 with <| scopes := [env]; gas_obs := gx |> =
   es0 with gas_obs := gx` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  simp[] >>
  Cases_on `res` >> simp[] >>
  rename1 `eval_stmts _ _ _ = (INR exc, ee)` >>
  Cases_on `exc` >> simp[] >>
  Cases_on `evaluate_type (type_env tops) ret` >> simp[] >>
  rename1 `safe_cast tv v` >> Cases_on `safe_cast tv v` >> simp[]
QED
