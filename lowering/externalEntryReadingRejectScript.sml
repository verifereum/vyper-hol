Theory externalEntryReadingReject
Ancestors
  entryValueRejectFacts e2eDefs vyperCall vyperInterpreter vyperState vyperContext list pair

(* Rejection occurs before evaluation can consume any gas readings. *)
Theorem external_entry_reject_readings:
  source_deployment_rel tops am tx /\
  value_transfer_ok tx am.accounts /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  bind_arguments (type_env tops) args tx.args = SOME env /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
      <| outcomes := SOME os; requests := [] |>) = (INR e,st) ==>
  !gs. FST (call_external (SOME os) gs am tx) <>
    INR (Error (RuntimeError "msg.gas: no gas reading"))
Proof
  strip_tac >>
  drule_all send_call_value_rejects_only_nonpayable >> strip_tac >>
  `LENGTH tx.args = LENGTH args` by metis_tac[bind_arguments_length] >>
  gen_tac >>
  `call_external_trace (SOME os) gs am tx =
    (INR (Error (RuntimeError "not Payable")), am, [], [])` by
    (fs[source_deployment_rel_def] >>
     simp[call_external_trace_def, find_function_module_def,
          lookup_exported_function_def, get_self_code_def, get_module_code_def,
          initial_evaluation_context_def, call_external_function_trace_def,
          send_call_value_def, vyperStateTheory.bind_def,
          vyperStateTheory.ignore_bind_def, vyperStateTheory.check_def,
          vyperStateTheory.assert_def, vyperStateTheory.raise_def,
          initial_state_def]) >>
  drule call_external_trace_result >> simp[] >>
  disch_then SUBST1_TAC >> simp[]
QED
