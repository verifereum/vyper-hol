Theory loweringRuntimeBudgetSourceEntry
Ancestors
  sourceCallCount e2eDefs vyperLoweringCorrect compileVyper vyperInterpreter

Theorem supported_runtime_call_entry_exists:
  !tops rpolicy unit am tx ret vs obs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs ==>
    ?res st. call_entry_run vs.vs_outcomes obs am tx = SOME (res,st)
Proof
  rpt gen_tac >> strip_tac >>
  drule source_deployment_context >> strip_tac >>
  gvs[source_deployment_rel_def, valid_vyper_call_def] >>
  simp[call_entry_run_def, find_function_module_def,
    lookup_exported_function_def, vyperContextTheory.get_self_code_def] >>
  simp[fn_entry_run_def, initial_evaluation_context_def] >>
  metis_tac[pairTheory.PAIR]
QED
