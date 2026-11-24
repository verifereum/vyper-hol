Theory linkedRuntimeValueRejection
Ancestors
  arithmetic e2eModsDefs vyperContext vyperInterpreter vyperState

Theorem linked_external_value_reject_trace:
  source_deployment_rel_mods mods exps am tx /\
  ALOOKUP mods (ALOOKUP exps tx.function_name) = SOME tops /\
  lookup_function (ALOOKUP exps tx.function_name) tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) /\
  LENGTH tx.args <= LENGTH args /\
  LENGTH args - LENGTH tx.args <= LENGTH dflts /\
  mut <> Payable /\ tx.value <> 0 ==>
  !gobs. call_external_trace orc gobs am tx =
    (INR (Error (RuntimeError "not Payable")),am,[],[])
Proof
  simp[LET_THM, source_deployment_rel_mods_def] >> strip_tac >>
  Cases_on `ALOOKUP am.exports tx.target` >> gvs[] >>
  Cases_on `ALOOKUP exps tx.function_name` >>
  gvs[call_external_trace_def, find_function_module_def,
      lookup_exported_function_def, get_self_code_def, get_module_code_def,
      initial_evaluation_context_def, call_external_function_trace_def,
      send_call_value_def, bind_def, ignore_bind_def, check_def, assert_def,
      raise_def, initial_state_def, GSYM NOT_LESS]
QED
