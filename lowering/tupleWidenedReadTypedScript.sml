(* Runtime typing at the physical tuple layout of a widened call. *)
Theory tupleWidenedReadTyped
Ancestors
  tupleWidenedSourceReady exprSimSource exprSimHyps exprSimHypsDefs
  valueEncodingTyping loweringPosts vyperTyping vyperState
Libs
  monadsyntax

Theorem tuple_widened_read_typed:
  !ce cx env e es obs tys stys stvs v ee.
    expr_body_pre ce cx env e es /\ expr_type e = TupleT tys /\
    lowered_value_type ce e <> expr_type e /\
    post_value_type ce e = TupleT stys /\
    evaluate_type (get_tenv cx) (TupleT stys) = SOME (TupleTV stvs) /\
    (do r <- eval_expr cx e; read_result cx r od)
      (es with gas_obs := obs) = (INL v,ee) ==>
    value_has_type (TupleTV stvs) v /\ val_wf (TupleTV stvs) v /\
    expr_sim_inv ce cx env ee
Proof
  rpt gen_tac >> strip_tac >>
  `expr_body_pre ce cx env e (es with gas_obs := obs)` by simp[] >>
  drule_all tuple_widened_source_ready >> strip_tac >> gvs[] >>
  drule_at (Pos last) ifexp_intcall_read_physical_typed >>
  simp[] >> disch_then drule >> strip_tac >> gvs[] >>
  drule_at (Pos last) expr_body_pre_eval >> simp[] >>
  disch_then drule >> strip_tac >>
  metis_tac[value_has_type_val_wf]
QED
