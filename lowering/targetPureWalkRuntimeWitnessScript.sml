Theory targetPureWalkRuntimeWitness
Ancestors
  targetPureWalkWitness exprLoweringProps

(* The shared entry fixture currently uses the genesis transaction. *)
Theorem w_entry_tx_env_obstruction:
  ~tx_env_ok w_cx.txn
Proof
  simp[loweringStateRelDefsTheory.tx_env_ok_def, w_cx_def,
       vyperContextTheory.empty_evaluation_context_def,
       vyperContextTheory.empty_call_txn_def]
QED

Theorem w_entry_relation_obstruction:
  ~stmt_state_rel w_ctx w_func w_cenv w_cx w_es w_s0
Proof
  simp[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def,
       loweringStateRelDefsTheory.call_ctx_rel_def,
       w_entry_tx_env_obstruction]
QED
