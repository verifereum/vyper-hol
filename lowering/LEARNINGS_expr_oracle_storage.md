# LEARNINGS_expr_oracle_storage

Reusable proof patterns only. Greppable structured entries; evidence refs point to episodes/tool outputs/source.

## L0001 scope='C1.4' tags=oracle_storage_entry_suffix,outcome_suffix,recursive_entry
shape: Sequential recursive evaluation needs IS_SOME outcomes and oracle_storage_ok in its intermediate state.
pattern: Prove the conjunction using irule oracle_storage_entry_suffix, witness the prior state, and derive suffix from the relevant eval_outcome_suffix_mutual conjunct. This avoids custom ML assumption scanning and handles consumed oracle prefixes.
works_when: The recursive evaluator equation is available and the parent entry has oracle mode and validity.
evidence:
- source:lowering/exprOracleStoragePreservationScript.sml:Base_SubscriptTarget
- source:lowering/exprOracleStoragePreservationScript.sml:Results_cons
- tool_output:TO_expr_oracle_storage-20261029T191510Z_m0127_t001

## L0002 scope='C1.4' tags=drule_all,call_evaluation_safe,gvs
shape: Exported typing boundary fails to match after empty internal-call simplification.
pattern: gvs may replace call_evaluation_safe cx (int_calls_target bt) with call_evaluation_safe cx []. Reintroduce the syntactic premise using `call_evaluation_safe cx (int_calls_target bt)` by simp[] before drule_all; no new semantic assumption is required.
works_when: int_calls_target bt = [] and call_evaluation_safe cx [] remain in context.
evidence:
- tool_output:TO_expr_oracle_storage-20261029T191510Z_m0117_t001
- tool_output:TO_expr_oracle_storage-20261029T191510Z_m0119_t001
