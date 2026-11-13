Theory initialVenomStateRel
Ancestors
  e2eDefs loweringStateRelDefs immutableSectionRel ptrDiscipline
  venomState finite_map

Definition venom_env_rel_def:
  venom_env_rel tx vs <=>
    loweringStateRelDefs$call_ctx_rel tx vs.vs_call_ctx vs.vs_tx_ctx vs.vs_block_ctx /\
    ~vs.vs_call_ctx.cc_static /\
    ~tx.is_static /\
    vs.vs_prev_hashes = tx.block_hashes
End

Definition initial_venom_state_rel_def:
  initial_venom_state_rel tops am tx vs <=>
    value_transfer_ok tx am.accounts /\
    vs.vs_accounts = accounts_after_transfer tx am.accounts /\
    vs.vs_transient = am.tStorage /\ am.logs = [] /\ vs.vs_logs = [] /\
    am.pending_deletions = [] /\
    tx_env_ok tx /\ venom_env_rel tx vs /\
    vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\ vs.vs_memory = [] /\
    vs.vs_allocas = FEMPTY /\ vs.vs_alloca_next = 0 /\
    vs.vs_returndata = [] /\ vs.vs_requests = [] /\
    vs.vs_pending_deletions = am.pending_deletions /\
    immutables_section_rel tops (account_immutables am tx.target) vs.vs_data_section
End

Theorem initial_ptr_allocations:
  initial_venom_state_rel tops am tx s ==>
  s.vs_allocas = FEMPTY /\ s.vs_alloca_next = 0 /\
  s.vs_vars = FEMPTY /\ s.vs_memory = [] /\ allocas_from 0 s
Proof
  simp[initial_venom_state_rel_def, allocas_from_def]
QED
