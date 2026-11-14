Theory abiDecodePtrRejectOutcome
Ancestors
  abiDecodePtrComplexOutcomeAbort abiDecodePtrAbortReentry abiDecodePtrRejectChecks
  abiDecoderReentry abiDecoderVarExtend abiDecodePtrMemberInterface
  abiDecoderCoherence abiDecoderMemberInfos abiEncoder compileEnv fragExec
  fragGasPathPtr venomExecSemantics venomState venomInst list words
  gasSummaryComposePtr gasSummary gasCount exprSimDefs vyperState vyperInterpreter

(* Counted rejecting suffixes; exemptions remain whole-expression facts. *)
Theorem ptr_runtime_error_abort_summary:
  (!tail. source (ee with gas_obs := tail) =
    (INR (Error (RuntimeError msg)), ee with gas_obs := tail)) /\
  gas_path_ptr D 0 ctx func PG G tn s n H tk (Abort a t) ==>
  gas_summary_ptr_at D (ctx,func) PG (REPLICATE n F) source
    (ee,s,G,tn) Q (\res ef gt r. expr_exit res r /\ halt_exit cx ef res r)
Proof
  strip_tac >> rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl [`INR (Error (RuntimeError msg))`, `ee`, `H`, `tk`, `Abort a t`] >>
  simp[exit_result_def, expr_exit_def] >>
  irule gas_marked_exec_ptr_no_source_read >> simp[]
QED

Theorem type_builtin_runtime_error_abort_summary:
  evaluate_type_builtin cx tb typ arg_tys args = INR (RuntimeError msg) /\
  gas_path_ptr D 0 ctx func PG G tn s n H tk (Abort a t) ==>
  gas_summary_ptr_at D (ctx,func) PG (REPLICATE n F)
    (bind (lift_sum (evaluate_type_builtin cx tb typ arg_tys args))
      (\w. return (Value w))) (ee,s,G,tn) Q
    (\res ef gt r. expr_exit res r /\ halt_exit cx ef res r)
Proof
  strip_tac >> irule ptr_runtime_error_abort_summary >>
  simp[lift_sum_def, bind_def, raise_def] >> metis_tac[]
QED
