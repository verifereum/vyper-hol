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

(* Separate witness constants preserve the checked zero-block experiment. *)
Definition order_runtime_cx_def:
  order_runtime_cx = order_ptr_cx with txn :=
    order_ptr_cx.txn with <|block_number := 1; block_hashes := [0w]|>
End

Definition order_runtime_start_def:
  order_runtime_start = order_ptr_start with vs_block_ctx :=
    order_ptr_start.vs_block_ctx with bc_number := 1w
End

Theorem order_runtime_tx_ok:
  tx_env_ok order_runtime_cx.txn
Proof
  EVAL_TAC
QED

Theorem order_runtime_call_context:
  call_ctx_rel order_runtime_cx.txn order_runtime_start.vs_call_ctx
    order_runtime_start.vs_tx_ctx order_runtime_start.vs_block_ctx
Proof
  EVAL_TAC >> rw[] >> gvs[]
QED

