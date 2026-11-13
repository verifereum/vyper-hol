(* The physical tuple type is available directly from a pointer-marked read. *)
Theory tupleWidenedMarkedReadPtr
Ancestors tupleWidenedReadTyped gasSummaryComposePtr exprSimHypsDefs
  loweringPosts list
Libs monadsyntax

Theorem tuple_widened_marked_read_typed_ptr:
  !ce cx env e es tys stys stvs D ctx func PG s0 G0 tn0 marks v ee G tn t.
    expr_body_pre ce cx env e es /\ expr_type e = TupleT tys /\
    lowered_value_type ce e <> expr_type e /\
    post_value_type ce e = TupleT stys /\
    evaluate_type (get_tenv cx) (TupleT stys) = SOME (TupleTV stvs) /\
    gas_marked_exec_ptr D (ctx,func) PG
      (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
      marks (INL v) ee G tn (OK t) ==>
    value_has_type (TupleTV stvs) v /\ val_wf (TupleTV stvs) v /\
    expr_sim_inv ce cx env (ee with gas_obs := [])
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_marked_exec_ptr_def]) >> strip_tac >>
  qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
  pure_rewrite_tac[APPEND_NIL] >> disch_tac >>
  drule_at (Pos last)
    (CONV_RULE (DEPTH_CONV ETA_CONV) tuple_widened_read_typed) >> simp[] >>
  disch_then drule >> gvs[]
QED
