Theory vyperExternalDefaultsTest
Ancestors
  vyperInterpreter vyperContext vyperState vyperAST vyperValueOperation
  vyperValue vyperRuntimeAccounts

(* Even a caller that already has locals cannot expose them to defaults. *)
Theorem external_default_empty_scope_test:
  eval_external_defaults cx [Name NoneT "a"] st =
    (INR (Error (TypeError "Name not in scope")), st)
Proof
  simp[eval_external_defaults_run, evaluate_def, get_scopes_def,
       lookup_scopes_val_def, lookup_scopes_def, lift_option_type_def,
       lift_option_def, type_check_def, assert_def,
       bind_def, ignore_bind_def, return_def, raise_def]
QED

(* The original error is propagated, rather than replaced with the old generic
   "call evaluate_defaults" RuntimeError. *)
Theorem external_default_exception_test:
  eval_external_defaults cx
    [Call NoneT RawRevert [Literal NoneT (BytesL [])] NONE] st =
    (INR (Error (RuntimeError "raw_revert")), st)
Proof
  simp[eval_external_defaults_run, evaluate_def, evaluate_literal_def,
       read_result_def, type_check_def, assert_def, bind_def,
       ignore_bind_def, return_def, raise_def]
QED

(* Account reads observe exactly the supplied state (in particular, the state
   after send_call_value), not the abstract machine from before the transfer. *)
Theorem external_default_balance_test:
  eval_external_defaults cx
    [Builtin (BaseT (UintT 256)) (Acc Balance)
      [Literal NoneT (BytesL bs)]] st =
    (INL [IntV &(lookup_account (word_of_bytes_be bs) st.accounts).balance], st)
Proof
  simp[eval_external_defaults_run, evaluate_def, evaluate_literal_def,
       read_result_def, builtin_args_length_ok_def,
       evaluate_builtin_def, evaluate_account_op_def,
       type_check_def, assert_def, get_accounts_def,
       lift_sum_def, bind_def, ignore_bind_def, return_def, raise_def]
QED

Theorem external_default_after_transfer_test:
  send_call_value Payable cx st = (INL (), transferred) ==>
  (do send_call_value Payable cx;
      eval_external_defaults cx
        [Builtin (BaseT (UintT 256)) (Acc Balance)
          [Literal NoneT (BytesL bs)]] od) st =
    (INL [IntV &(lookup_account (word_of_bytes_be bs)
                  transferred.accounts).balance], transferred)
Proof
  strip_tac >> simp[bind_def, ignore_bind_def, external_default_balance_test]
QED

(* Whatever effects the first default has (storage, balances, logs, oracle
   requests), the next default observes them and they survive the evaluation.
   This symbolic probe is stronger than choosing a particular storage write. *)
Theorem external_defaults_state_threading_test:
  eval_expr cx e (st with scopes := [FEMPTY]) = (INL (Value v), changed) ==>
  eval_external_defaults cx
    [e; Builtin (BaseT (UintT 256)) (Acc Balance)
          [Literal NoneT (BytesL bs)]] st =
    (INL [v; IntV &(lookup_account (word_of_bytes_be bs) changed.accounts).balance],
     changed with scopes := st.scopes)
Proof
  strip_tac >>
  simp[eval_external_defaults_cons, evaluate_def, evaluate_literal_def,
       read_result_def, builtin_args_length_ok_def,
       evaluate_builtin_def, evaluate_account_op_def,
       type_check_def, assert_def, get_accounts_def,
       lift_sum_def, bind_def, ignore_bind_def, return_def, raise_def]
QED

(* Fail the regression build if any boundary or probe acquires an admission. *)
val () = List.app (fn th =>
  if List.null (List.filter (fn s => s <> "DISK_THM")
      (#1 (Tag.dest_tag (Thm.tag th)))) then ()
  else raise Fail "external defaults boundary has oracle dependencies")
  [eval_external_defaults_run, eval_external_defaults_nil,
   eval_external_defaults_length, eval_external_defaults_cons,
   eval_external_defaults_cons_success, eval_external_defaults_error,
   eval_external_defaults_scopes,
   external_default_empty_scope_test, external_default_exception_test,
   external_default_balance_test, external_default_after_transfer_test,
   external_defaults_state_threading_test];
