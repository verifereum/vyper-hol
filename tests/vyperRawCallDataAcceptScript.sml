Theory vyperRawCallDataAccept
Ancestors
  vyperRawCallDataAcceptEval

(* WHY THIS IS TRUE: A dynamic Bytes operand already has the pointer
   representation required by RawCallTarget. Neither an ordinary Bytes[32]
   argument nor an empty bytes literal should be lost by the restriction.
   In particular the zero bound here is an expression annotation, not a new
   declared-type policy. These are full-contract positive controls in both
   checker modes; they make no assertion about compiler correctness. *)
Theorem raw_call_dynamic_and_empty_contracts_accepted:
  !in_deploy.
    IS_SOME (check_contract in_deploy [] (0w : address)
      (raw_data_modules (BaseT (BytesT (Dynamic 32))))) /\
    IS_SOME (check_contract in_deploy [] (0w : address) raw_empty_modules)
Proof
  Cases >> simp[raw_data_dynamic_deploy_eval, raw_data_dynamic_runtime_eval,
                raw_data_empty_deploy_eval, raw_data_empty_runtime_eval]
QED
