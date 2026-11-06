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

Theorem abi_decode_realize_outcome_needs_normal:
  gas_outcome memory tops (ctx,func)
    (eval_expr (abi_decode_realize_live_cx k) (abi_decode_realize_expr k))
    (es,s0) Q (\res ee r. exprSimDefs$expr_exit res r) ==>
  ?n t res ee. gas_path ctx func s0 n (OK t) /\ Q (INL res) ee t
Proof
  simp[gas_outcome_def, abi_decode_realize_no_exempt,
       gas_summary_at_def, gas_marked_exec_def] >>
  rpt strip_tac >>
  strip_assume_tac abi_decode_realize_live_eval >>
  qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >> simp[] >>
  strip_tac >> gvs[] >>
  gvs[exprSimDefsTheory.expr_exit_INL] >>
  drule fragGasModeTheory.gas_marked_path_exec >>
  metis_tac[]
QED
