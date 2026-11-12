Theory targetPureWalkRuntimeWitness
Ancestors
  targetPureWalkWitness exprLoweringProps

(* The concrete transaction has a valid one-block hash window. *)
Theorem w_tx_env_ok:
  tx_env_ok w_cx.txn
Proof
  EVAL_TAC
QED

(* All call, transaction and block fields match, including BLOCKHASH. *)
Theorem w_call_ctx_rel:
  call_ctx_rel w_cx.txn w_s0.vs_call_ctx w_s0.vs_tx_ctx w_s0.vs_block_ctx
Proof
  simp[loweringStateRelDefsTheory.call_ctx_rel_def, w_tx_env_ok,
       w_cx_def, w_s0_def,
       vyperContextTheory.empty_evaluation_context_def,
       vyperContextTheory.empty_call_txn_def,
       venomStateTheory.init_venom_state_def,
       venomStateTheory.empty_call_context_def,
       venomStateTheory.empty_tx_context_def,
       venomStateTheory.empty_block_context_def] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[] >> gvs[]
QED
