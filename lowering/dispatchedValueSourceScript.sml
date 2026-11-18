(* Source rejection precedes argument binding, defaults and body execution. *)
Theory dispatchedValueSource
Ancestors sourceValueRejection vyperCall e2eDefs vyperInterpreter vyperState
  vyperContext

Theorem source_dispatched_value_reject_error:
  source_deployment_rel tops am tx /\
  value_transfer_ok tx am.accounts /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with <|outcomes := SOME os; requests := []|>) =
    (INR e,st) ==>
  e = Error (RuntimeError "not Payable")
Proof
  rpt strip_tac >>
  `tx.value <> 0 /\ mut <> Payable` by
    (drule_at (Pos last) send_call_value_reject_condition >>
     simp[initial_evaluation_context_def, initial_state_def]) >>
  gvs[send_call_value_def, initial_evaluation_context_def,
      bind_def, ignore_bind_def, check_def, assert_def]
QED

Theorem source_dispatched_value_reject_trace:
  source_deployment_rel tops am tx /\
  value_transfer_ok tx am.accounts /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with <|outcomes := SOME os; requests := []|>) =
    (INR e,st) ==>
  !gobs. call_external_trace (SOME os) gobs am tx = (INR e,am,[],[])
Proof
  rpt strip_tac >>
  `e = Error (RuntimeError "not Payable")` by
    metis_tac[source_dispatched_value_reject_error] >>
  `tx.value <> 0 /\ mut <> Payable` by
    (drule_at (Pos last) send_call_value_reject_condition >>
     simp[initial_evaluation_context_def, initial_state_def]) >>
  `LENGTH args = LENGTH tx.args` by metis_tac[bind_arguments_length] >>
  gvs[source_deployment_rel_def] >>
  simp[call_external_trace_def, find_function_module_def,
       lookup_exported_function_def, get_self_code_def, get_module_code_def,
       initial_evaluation_context_def, call_external_function_trace_def,
       send_call_value_def, bind_def, ignore_bind_def, check_def, assert_def,
       initial_state_def]
QED
