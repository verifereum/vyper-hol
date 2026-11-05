(* Unit-normalized certificate transport for result-valued source binds.
   These rules preserve exemption evidence, not ordinary gas summaries. *)
Theory bodyIntCallJointBind
Ancestors
  gasOutcome gasExemptCert vyperState vyperInterpreter

Theorem joint_exempt_result_error:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (a : evaluation_state -> eval_result evaluation_result)
      (return ())) (es,s0) marks (err,ee) (leaf,finstate) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind a k) (return ()))
    (es,s0) marks (err,ee) (leaf,finstate)
Proof
  rewrite_tac[ignore_bind_def, bind_assoc] >> strip_tac >>
  irule gas_exempt_cert_error_result >>
  gvs[ignore_bind_def]
QED

Theorem joint_exempt_result_bind:
  gas_marked_exec memory (ctx,func)
    (a : evaluation_state -> eval_result evaluation_result)
    (es,s0) left (INL v) mid (OK t) /\
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (k v) (return ()))
    (mid with gas_obs := [],t) right (err,ee) (leaf,finstate) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind a k) (return ()))
    (es,s0) (left ++ right) (err,ee) (leaf,finstate)
Proof
  rewrite_tac[ignore_bind_def, bind_assoc] >> strip_tac >>
  irule gas_exempt_cert_bind_result >>
  qexistsl [`mid`, `t`, `v`] >> simp[]
QED
