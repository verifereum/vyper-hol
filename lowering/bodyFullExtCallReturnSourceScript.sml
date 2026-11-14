(* Return decoding preserves the source state, including arbitrary observations. *)
Theory bodyFullExtCallReturnSource
Ancestors
  vyperInterpreter vyperABI vyperState

Theorem extcall_return_source_tail:
  !cx ret_type returnData default_opt skip target ee.
    ?res. !tail.
      (case (if returnData = [] then default_opt else NONE) of
         SOME default_v =>
           do accounts' <- get_accounts;
              check (skip \/ ext_call_has_code target accounts')
                    "ExtCall target has no code";
              return (Value default_v)
           od
       | NONE =>
           do ret_val <- lift_sum_runtime
                (evaluate_abi_decode_return (get_tenv cx) ret_type returnData);
              return (Value ret_val)
           od) (ee with gas_obs := tail) =
         (res, ee with gas_obs := tail)
Proof
  rpt gen_tac >>
  Cases_on `if returnData = [] then default_opt else NONE`
  >- (Cases_on `evaluate_abi_decode_return (get_tenv cx) ret_type returnData` >>
      simp[bind_def, lift_sum_runtime_def, return_def, raise_def]) >>
  Cases_on `skip \/ ext_call_has_code target ee.accounts` >>
  simp[get_accounts_def, bind_def, ignore_bind_def, check_def,
       assert_def, return_def]
QED
