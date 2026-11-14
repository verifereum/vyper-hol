(* Ordinary constructor callbacks need effect-freedom, not a recursively
   inherited body_expr_ok.  Ownership callbacks remain separate. *)
Theory bodyIntCallPostProvenanceCallbacks
Ancestors bodyExprPreFacts supportedExprTraverse vyperInterpreter vyperState

Theorem effect_free_int_calls:
  !e. ~expr_has_effect e ==> int_calls_expr e = []
Proof
  rpt strip_tac >>
  `!x. expr_internal_call_root x ==> expr_effect_root x` by
    (Cases >> simp[expr_internal_call_root_def, expr_effect_root_def]) >>
  `~supported_expr_exists expr_internal_call_root e` by
    metis_tac[cj 1 supported_expr_exists_mono, expr_has_effect_def] >>
  metis_tac[cj 1 no_internal_call_int_calls]
QED

(* In the capture case the read is before, not after, index evaluation. *)
Theorem eval_expr_subscript_capture_bind:
  subscript_reads_base cx obj idx ==>
  eval_expr cx (Subscript ann obj idx) =
  bind (eval_expr cx obj) (\r.
    bind (read_result cx r) (\v.
      bind (bind (eval_expr cx idx) (read_result cx)) (\i.
        select_result cx (expr_type obj) (Value v) (ValueSubscript i))))
Proof
  strip_tac >> simp[Once evaluate_def, bind_assoc] >>
  simp[FUN_EQ_THM, bind_def, return_def]
QED
