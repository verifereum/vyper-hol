(* Arbitrary-horizon initialization at the runtime body boundary. *)
Theory defaultEntryState
Ancestors
  entryStateRel e2eDefs immutableSectionRel loweringStateRelDefs
  vyperState vyperLoweringCorrect vyperInterpreter venomState

Theorem default_body_state_rel:
  !(H:(bool # bytes32 # type_value) list # num list) tops func cenv cx am tx vs ss mut env es.
    initial_venom_state_rel tops am tx vs /\ cx.txn = tx /\
    send_call_value mut cx
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) = (INL (), es) /\
    ss.vs_accounts = vs.vs_accounts /\ ss.vs_transient = vs.vs_transient /\
    ss.vs_logs = vs.vs_logs /\ ss.vs_call_ctx = vs.vs_call_ctx /\
    ss.vs_tx_ctx = vs.vs_tx_ctx /\ ss.vs_block_ctx = vs.vs_block_ctx /\
    ss.vs_outcomes = vs.vs_outcomes /\ ss.vs_requests = vs.vs_requests /\
    ss.vs_pending_deletions = vs.vs_pending_deletions /\
    ss.vs_code = vs.vs_code /\
    local_ptrs_rel func cenv [env] ss /\
    storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
    cenv.ce_module = NONE /\ ~cenv.ce_is_ctor /\
    immutable_section_layout cenv tops /\ ss.vs_data_section = vs.vs_data_section ==>
    state_rel H func cenv cx es ss
Proof
  rpt gen_tac >> strip_tac >>
  drule send_call_value_accounts >> strip_tac >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es ss` by
    (gvs[] >> irule immutables_section_rel_runtime_fallback >>
     gvs[initial_venom_state_rel_def, initial_state_def, account_immutables_def] >>
     qexists_tac `tops` >> simp[]) >>
  gvs[initial_venom_state_rel_def, venom_env_rel_def, state_rel_def,
      initial_state_def] >>
  `ss.vs_call_ctx.cc_address = cx.txn.target` by fs[call_ctx_rel_def] >>
  simp[storage_rel_def, transient_rel_def, contract_storage_def,
       contract_transient_def, logs_rel_def, accounts_rel_def]
QED
