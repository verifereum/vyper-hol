Theory s1PrefixSelectedTrace
Ancestors
  s1PrefixSelectedBoundFrame s1PrefixSelectedCallSuffix
  s1PrefixIntCallCalleeLocked

Theorem selected_prefix_trace_alignment:
  lower_vyper_runtime_unit tops rp = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) /\
  (!gx. external_entry_bound tops am tx os (prefix ++ gx) mut args dflts
    (es0 with gas_obs := gx)) /\
  lock_if_nr cx nr (is_view_mut mut) es0 = (INL (),es_lock) /\
  (!gx. eval_stmts cx compiled_body (es_lock with gas_obs := gx) =
        eval_stmts cx fbody (es_lock with gas_obs := gx)) ==>
  es_lock.requests = [] /\ recorded_outcomes_count es_lock.storage_trace = 0 /\
  (!gas r am' rqs obs.
    call_external_trace (SOME os) (prefix ++ gas) am tx = (r,am',rqs,obs) ==>
    ?ans ee suffix.
      eval_stmts cx compiled_body (es_lock with gas_obs := gas) = (ans,ee) /\
      obs = ee.storage_trace ++ suffix /\ recorded_outcomes_count suffix = 0)
Proof
  strip_tac >>
  qpat_assum `!gx. external_entry_bound _ _ _ _ _ _ _ _ _`
    (qspec_then `[]` assume_tac) >>
  drule_all selected_bound_request_frame >> simp[] >> strip_tac >>
  drule intcall_callee_lock_request_frame >> strip_tac >>
  conj_tac >- simp[] >>
  conj_tac >- (Cases_on `nr` >> simp[e2eRequestCutDefsTheory.recorded_outcomes_count_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!gx. external_entry_bound _ _ _ _ _ _ _ _ _`
    (qspec_then `gas` assume_tac) >>
  drule_all selected_bound_call_trace_suffix >> strip_tac >>
  qexists_tac `ans` >> qexists_tac `ee` >> qexists_tac `suffix` >>
  gvs[]
QED
