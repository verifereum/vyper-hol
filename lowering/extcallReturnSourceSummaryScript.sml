(* Packaging the counted return decoder paths against its source computation. *)
Theory extcallReturnSourceSummary
Ancestors
  extcallReturnCallerSuccess extcallReturnCallerReject gasSummary
  exprSimDefs fragExec vyperState vyperABI venomState venomExecSemantics list

Theorem return_decode_counted_summary:
  (!v. evaluate_abi_decode_return env ty bs = INL v ==>
     ?z. gas_marked_path F ctx func s 0 (OK z) /\
         Q (INL (Value v)) (ee with gas_obs := []) z) /\
  (!err. evaluate_abi_decode_return env ty bs = INR err ==>
     ?z. gas_marked_path F ctx func s 0 (Abort Revert_abort z)) ==>
  gas_summary_at F (ctx,func) []
    (do v <- lift_sum_runtime (evaluate_abi_decode_return env ty bs);
        return (Value v) od) (ee,s) Q (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  Cases_on `evaluate_abi_decode_return env ty bs` >> gvs[]
  >- (simp[gas_summary_at_def, gas_marked_exec_def, lift_sum_runtime_def,
           bind_def, return_def] >>
      qexistsl_tac [`INL (Value x)`, `ee`, `OK z`] >> simp[] >> metis_tac[]) >>
  simp[gas_summary_at_def, gas_marked_exec_def, lift_sum_runtime_def,
       bind_def, return_def, raise_def] >>
  qexistsl_tac [`INR (Error (RuntimeError y))`, `ee`, `Abort Revert_abort z`] >>
  simp[expr_exit_def, exit_result_def]
QED
