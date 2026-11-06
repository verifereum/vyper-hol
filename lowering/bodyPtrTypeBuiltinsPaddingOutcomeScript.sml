(* Outcome-exclusion probes for the padding witness. *)
Theory bodyPtrTypeBuiltinsPaddingOutcome
Ancestors
  bodyPtrTypeBuiltinsPaddingFrame bodyPtrTypeBuiltinsPaddingTarget
  gasExemptCert vyperState vyperInterpreter words

Theorem padding_source_returns:
  bind (eval_expr padding_actual_context padding_expr)
    (read_result padding_actual_context) (padding_source with gas_obs := gs) =
  (INL (IntV 0), padding_source with gas_obs := gs)
Proof
  EVAL_TAC >> CONV_TAC (DEPTH_CONV wordsLib.WORD_CONV) >> simp[] >> EVAL_TAC
QED

Theorem padding_no_exempt_cert:
  ~gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr padding_actual_context padding_expr)
                  (read_result padding_actual_context)) (return ()))
    (padding_source,s) marks (err,ee) (leaf,final_s)
Proof
  strip_tac >> drule gas_exempt_cert_execution >>
  simp[ignore_bind_def, bind_def, padding_source_returns, return_def]
QED
