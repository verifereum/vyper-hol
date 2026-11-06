Theory bodyPtrPopFullFrameRuntime
Ancestors
  bodyPtrPopFullFrameProbe compileEnv exprLoweringProps vyperContext

(* Positive domain probe for the repaired control transaction; no runtime
   relation witness or target execution is asserted here. *)
Theorem pop_full_frame_transaction_domain:
  tx_env_ok pop_full_frame_cx.txn
Proof
  EVAL_TAC
QED
