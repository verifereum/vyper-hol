Theory ctorDeployMemoryRunMemEntrySourceWorld
Ancestors
  ctorDeployMemoryRunMemEntrySourceDefaults ctorDeployLoweringEntrySourceFrame
  ctorDeployLoweringFrame ctorDeployLoweringDefs ctorDeployLoweringEntryTransport
  ctorDeployDefs e2eDeployDefs e2eDefs compileEnv venomState accountsRelProps e2eEntry
  o1PassContract

(* World conjuncts of state_rel: storage_rel, transient_rel, accounts_rel,
   logs_rel, call_ctx_rel, nonstatic flags, outcomes, request agreement and
   pending deletions. No execution endpoint is selected by these boundaries. *)
Theorem ctor_source_start_world_fields:
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) ==>
  es0.tStorage = am.tStorage /\ es0.logs = [] /\
  es0.requests = [] /\ es0.pending_deletions = [] /\
  es0.immutables = am_c.immutables /\ es0.outcomes = NONE /\
  es0.accounts = accounts_after_transfer tx am.accounts
Proof
  strip_tac >>
  `~nr` by metis_tac[deploy_ctor_not_nonreentrant] >> gvs[] >>
  `?args scope.
    lookup_function NONE tx.function_name Deploy tops =
      SOME (mut,F,args,[],NoneT,stmts) /\
    bind_arguments (type_env tops) args tx.args = SOME scope` by
    gvs[deploy_ctor_start_def, deploy_ctor_singleton_type_env] >>
  pop_assum strip_assume_tac >>
  drule_all deploy_ctor_source_start_fields >> strip_tac >>
  drule_all deploy_ctor_source_start_accounts >> strip_tac >>
  gvs[deploy_state_rel_def, accounts_after_transfer_def]
QED

Theorem ctor_source_landing_world:
  deploy_source_ok tops am tx /\
  deploy_state_rel tops deploy_bc am tx es /\
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) /\
  actual.vs_accounts = accounts_after_transfer tx am.accounts /\
  actual.vs_transient = am.tStorage /\
  actual.vs_call_ctx.cc_address = tx.target /\
  actual.vs_logs = [] /\ actual.vs_requests = [] /\
  actual.vs_pending_deletions = [] ==>
  storage_rel (deploy_evaluation_context tops am tx) tx.target
    (es0 with outcomes := SOME os) actual /\
  transient_rel (deploy_evaluation_context tops am tx) tx.target
    (es0 with outcomes := SOME os) actual /\
  accounts_rel (deploy_evaluation_context tops am tx)
    (es0 with outcomes := SOME os) actual /\
  logs_rel cenv tx.target (es0 with outcomes := SOME os) actual /\
  LIST_REL (request_agree (deploy_evaluation_context tops am tx))
    (es0 with outcomes := SOME os).requests actual.vs_requests /\
  (es0 with outcomes := SOME os).pending_deletions = actual.vs_pending_deletions
Proof
  strip_tac >> drule_all ctor_source_start_world_fields >> strip_tac >>
  simp[storage_rel_def, transient_rel_def, accounts_rel_def, logs_rel_def,
       contract_storage_def, contract_transient_def]
QED

Theorem ctor_source_entry_context:
  deploy_state_rel tops deploy_bc am tx es ==>
  call_ctx_rel tx
    (deploy_entry_state prog cplan tops es).vs_call_ctx
    (deploy_entry_state prog cplan tops es).vs_tx_ctx
    (deploy_entry_state prog cplan tops es).vs_block_ctx /\
  ~(deploy_entry_state prog cplan tops es).vs_call_ctx.cc_static /\
  ~tx.is_static
Proof
  simp[deploy_state_rel_def, deploy_entry_state_def, entry_venom_state_def,
       call_ctx_rel_def, tx_block_fields_rel_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem ctor_source_candidate_context:
  deploy_state_rel tops deploy_bc am tx es /\
  gas_variant vs (deploy_entry_state prog cplan tops es) /\
  actual.vs_call_ctx = vs.vs_call_ctx /\
  actual.vs_tx_ctx = vs.vs_tx_ctx /\
  actual.vs_block_ctx = vs.vs_block_ctx /\
  actual.vs_outcomes = vs.vs_outcomes ==>
  call_ctx_rel tx actual.vs_call_ctx actual.vs_tx_ctx actual.vs_block_ctx /\
  ~actual.vs_call_ctx.cc_static /\ ~tx.is_static /\
  (es0 with outcomes := SOME vs.vs_outcomes).outcomes = SOME actual.vs_outcomes
Proof
  strip_tac >> drule ctor_source_entry_context >>
  disch_then (qspecl_then [`prog`,`cplan`] mp_tac) >>
  qpat_x_assum `gas_variant _ _` mp_tac >>
  simp[gas_variant_def] >> disch_then SUBST1_TAC >> simp[]
QED

Theorem ctor_source_entry_world_projections:
  deploy_state_rel tops deploy_bc am tx es /\
  gas_variant vs (deploy_entry_state prog cplan tops es) ==>
  vs.vs_accounts = accounts_after_transfer tx am.accounts /\
  vs.vs_transient = am.tStorage /\
  vs.vs_call_ctx.cc_address = tx.target /\
  vs.vs_logs = [] /\ vs.vs_requests = [] /\
  vs.vs_pending_deletions = []
Proof
  strip_tac >>
  `((deploy_entry_state prog cplan tops es).vs_accounts =
       accounts_after_transfer tx am.accounts) /\
    (deploy_entry_state prog cplan tops es).vs_transient = am.tStorage /\
    (deploy_entry_state prog cplan tops es).vs_call_ctx.cc_address = tx.target /\
    (deploy_entry_state prog cplan tops es).vs_logs = [] /\
    (deploy_entry_state prog cplan tops es).vs_requests = [] /\
    (deploy_entry_state prog cplan tops es).vs_pending_deletions = []` by
    (gvs[deploy_state_rel_def, deploy_entry_state_def, entry_venom_state_def,
         init_venom_state_def]) >>
  qpat_x_assum `gas_variant _ _` mp_tac >>
  simp[gas_variant_def] >> disch_then SUBST_ALL_TAC >> gvs[]
QED
