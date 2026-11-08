Theory ctorDeployMemoryRunPtrPrefixEntryAmbient
Ancestors
  ctorDeployMemoryRunPtrPrefixEntrySemantic ctorDeployLoweringEntrySourceFrame
  ctorDeployDefs e2eDeployDefs e2eDefs e2eEntry compileEnv o1PassContract
  vyperInterpreter vyperState vyperContext accountsRelProps venomState

Theorem deploy_ptr_entry_source_accounts:
  !tops am tx mut body am_c es0 args scope.
  deploy_ctor_start tops am tx (mut,F,body,am_c,es0) /\
  lookup_function NONE tx.function_name Deploy tops =
    SOME (mut,F,args,[],NoneT,body) /\
  bind_arguments (type_env tops) args tx.args = SOME scope ==>
  es0.accounts = accounts_after_transfer tx am.accounts
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_ctor_source_start_accounts >>
  simp[accounts_after_transfer_def]
QED

Theorem deploy_ptr_entry_actual_state_rel:
  !tops bc am tx es vs prog cp rp runtime unit body ce nr key ut imm exit
    sa sb sj se sp sf func mut am_c es0 args scope actual.
  deploy_source_ok tops am tx /\ deploy_state_rel tops bc am tx es /\
  gas_variant vs (deploy_entry_state prog cp tops es) /\
  deploy_ctor_code tops rp runtime unit
    (body,ce,nr,key,ut,imm,exit,sa,sb,sj,se,sp,sf,func) /\
  deploy_ctor_start tops am tx (mut,F,body,am_c,es0) /\
  lookup_function NONE tx.function_name Deploy tops = SOME (mut,F,args,[],NoneT,body) /\
  bind_arguments (type_env tops) args tx.args = SOME scope /\
  actual.vs_accounts = vs.vs_accounts /\ actual.vs_transient = vs.vs_transient /\
  actual.vs_logs = vs.vs_logs /\ actual.vs_requests = vs.vs_requests /\
  actual.vs_pending_deletions = vs.vs_pending_deletions /\
  actual.vs_call_ctx = vs.vs_call_ctx /\ actual.vs_tx_ctx = vs.vs_tx_ctx /\
  actual.vs_block_ctx = vs.vs_block_ctx /\ actual.vs_outcomes = vs.vs_outcomes /\
  local_ptrs_rel func ce es0.scopes actual /\
  immutables_rel ce (deploy_evaluation_context tops am tx).txn.target
    ce.ce_module ce.ce_is_ctor (es0 with outcomes := SOME vs.vs_outcomes) actual ==>
  state_rel func ce (deploy_evaluation_context tops am tx)
    (es0 with outcomes := SOME vs.vs_outcomes) actual
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_ptr_ctor_storage_vars >> strip_tac >>
  drule_all deploy_ctor_source_start_fields >> strip_tac >>
  drule_all deploy_ptr_entry_source_accounts >> strip_tac >>
  gvs[state_rel_def, storage_rel_def, transient_rel_def, accounts_rel_def,
      logs_rel_def, deploy_evaluation_context_def, initial_evaluation_context_def] >>
  qpat_x_assum `gas_variant _ _` mp_tac >>
  rewrite_tac[gas_variant_def] >>
  disch_then (mp_tac o Q.AP_TERM `\s. (s.vs_accounts,s.vs_transient,s.vs_logs,
    s.vs_call_ctx,s.vs_tx_ctx,s.vs_block_ctx,s.vs_requests,s.vs_pending_deletions)`) >>
  simp[deploy_entry_state_def, entry_venom_state_def, init_venom_state_def] >>
  strip_tac >>
  gvs[deploy_state_rel_def] >>
  gvs[contract_storage_def, contract_transient_def, call_ctx_rel_def,
      tx_block_fields_rel_def] >>
  qpat_x_assum `_ = vs.vs_call_ctx` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `_ = vs.vs_tx_ctx` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `_ = vs.vs_block_ctx` (SUBST_ALL_TAC o SYM) >>
  simp[]
QED
