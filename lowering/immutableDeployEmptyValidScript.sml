(* Transaction-valid variant of the shared source fixture. *)
Theory immutableDeployEmptyValid
Ancestors
  immutableDeployEmptyStacked immutableDeployEmptyMachine compileEnv vyperContext

Definition empty_immutable_valid_cx_def:
  empty_immutable_valid_cx = empty_immutable_stacked_cx with
    txn := (empty_immutable_stacked_cx.txn with
      <|block_number := 1; block_hashes := [0w]|>)
End

Theorem empty_immutable_valid_tx_env:
  tx_env_ok empty_immutable_valid_cx.txn
Proof
  EVAL_TAC
QED
