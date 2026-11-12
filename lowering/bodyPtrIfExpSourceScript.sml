(* Raw selected-arm source transport.  This preserves the operand's
   exceptional certificate without inverting a forced-value certificate. *)
Theory bodyPtrIfExpSource
Ancestors
  gasExemptCert vyperInterpreter vyperState

Theorem ifexp_arm_ignore_bind_action[local]:
  ignore_bind (bind a (conditional_result cx)) (return ()) =
  bind a (\tv. ignore_bind (conditional_result cx tv) (return ()))
Proof
  simp[FUN_EQ_THM, ignore_bind_def, bind_def, return_def] >>
  gen_tac >> Cases_on `a x` >> Cases_on `q` >> simp[bind_def]
QED

Theorem ifexp_arm_exempt_transport:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind a (return ())) (es,s0) marks (err,ee) (leaf,finstate) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind a (conditional_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,finstate)
Proof
  rewrite_tac[ifexp_arm_ignore_bind_action] >> strip_tac >>
  irule gas_exempt_cert_error_result >> simp[]
QED
