Theory exprSimAbiDecodeRealizeCounted
Ancestors
  exprSimAbiDecodeRealizeEntry exprSimAbiDecodeRealizeTarget
  gasExemptCert gasOutcome gasSummary vyperState

Theorem abi_decode_realize_no_exempt:
  ~gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_expr (abi_decode_realize_live_cx k)
      (abi_decode_realize_expr k)) (return ()))
    (es,s0) marks (err,ee) (leaf,sfinal)
Proof
  strip_tac >> drule gas_exempt_cert_execution >>
  strip_tac >>
  strip_assume_tac abi_decode_realize_live_eval >>
  qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
  simp[ignore_bind_def, bind_def, return_def]
QED
