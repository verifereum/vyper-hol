(* Runtime source-entry state correspondence, including immutable data. *)
Theory entryReachBodyRuntimeState
Ancestors
  loweringStateRelDefs entryStateRel e2eDefs immutableSectionRel immutableRelation compileEnv
  vyperLoweringCorrect vyperInterpreter vyperState vyperContext venomState
  finite_map

Theorem entry_runtime_state_rel:
  initial_venom_state_rel tops am tx vs /\
  send_call_value mut (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
       <| outcomes := SOME vs.vs_outcomes; requests := [] |>) = (INL (), es) /\
  ss.vs_accounts = vs.vs_accounts /\ ss.vs_transient = vs.vs_transient /\
  ss.vs_logs = vs.vs_logs /\ ss.vs_call_ctx = vs.vs_call_ctx /\
  ss.vs_tx_ctx = vs.vs_tx_ctx /\ ss.vs_block_ctx = vs.vs_block_ctx /\
  ss.vs_outcomes = vs.vs_outcomes /\ ss.vs_requests = vs.vs_requests /\
  ss.vs_pending_deletions = vs.vs_pending_deletions /\
  local_ptrs_rel func cenv [env] ss /\
  storage_vars_rel cenv (initial_evaluation_context am.sources am.layouts tx NONE) /\
  transient_vars_rel cenv (initial_evaluation_context am.sources am.layouts tx NONE) /\
  cenv.ce_module = NONE /\ ~cenv.ce_is_ctor /\
  immutable_section_layout cenv tops /\ ss.vs_data_section = vs.vs_data_section ==>
  state_rel func cenv (initial_evaluation_context am.sources am.layouts tx NONE) es ss
Proof
  strip_tac >> drule send_call_value_accounts >> strip_tac >>
  `immutables_rel cenv tx.target NONE F es ss` by
    (irule immutables_section_rel_runtime_fallback >>
     gvs[initial_venom_state_rel_def, initial_state_def, account_immutables_def,
         initial_evaluation_context_def] >>
     qexists_tac `tops` >> simp[]) >>
  gvs[initial_venom_state_rel_def, venom_env_rel_def, state_rel_def,
      initial_state_def, initial_evaluation_context_def] >>
  `ss.vs_call_ctx.cc_address = tx.target` by fs[call_ctx_rel_def] >>
  simp[storage_rel_def, transient_rel_def, contract_storage_def,
       contract_transient_def, logs_rel_def, accounts_rel_def]
QED
