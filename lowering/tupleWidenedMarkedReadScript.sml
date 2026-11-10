(* Physical tuple typing behind a gas-marked successful read. *)
Theory tupleWidenedMarkedRead
Ancestors
  tupleWidenedReadiness gasSummary exprSimHypsDefs loweringPosts list
Libs
  monadsyntax

Theorem tuple_widened_marked_read_typed:
  !ce cx env e es tys stys stvs ctx func s0 marks v ee t.
    expr_body_pre ce cx env e es /\ expr_type e = TupleT tys /\
    lowered_value_type ce e <> expr_type e /\
    post_value_type ce e = TupleT stys /\
    evaluate_type (get_tenv cx) (TupleT stys) = SOME (TupleTV stvs) /\
    gas_marked_exec T (ctx,func) (bind (eval_expr cx e) (read_result cx))
      (es,s0) marks (INL v) ee (OK t) ==>
    value_has_type (TupleTV stvs) v /\ val_wf (TupleTV stvs) v /\
    expr_sim_inv ce cx env (ee with gas_obs := [])
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_marked_exec_def] >> strip_tac >>
  qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
  pure_rewrite_tac[APPEND_NIL] >> disch_tac >>
  drule_at (Pos last)
    (CONV_RULE (DEPTH_CONV ETA_CONV) tuple_widened_read_typed) >> simp[] >>
  disch_then drule >> gvs[]
QED
