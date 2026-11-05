Theory bodyPtrBytestringBuiltinsRuntime
Ancestors
  bodyPtrBytestringBuiltinsPtrFrame bodyPtrDefs

Theorem order_ptr_runtime_tx_obstruction:
  order_ptr_cx.txn.block_number = 0 /\
  ~tx_env_ok order_ptr_cx.txn
Proof
  EVAL_TAC
QED

Theorem order_ptr_runtime_no_state_rel:
  ~state_rel func order_ptr_env order_ptr_cx es s
Proof
  simp[compileEnvTheory.state_rel_def,
       compileEnvTheory.call_ctx_rel_def,
       order_ptr_runtime_tx_obstruction]
QED
