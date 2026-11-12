(* The relayout source is bounded by the RHS annotation, not by the
   destination local's declared capacity. *)
Theory placeRelayoutBounds
Ancestors
  assignRelayoutCaller exprSimHyps annassignRelayoutSource
  exprSimHypsDefs allocLimits words

Theorem expr_body_pre_relayout_source_bound:
  !cenv cx env e es sty stv.
    expr_body_pre cenv cx env e es /\
    ~is_word_type (expr_type e) /\
    type_widens_to (get_tenv cx) sty (expr_type e) /\
    evaluate_type (get_tenv cx) sty = SOME stv ==>
    type_memory_bytes cenv sty = type_memory_size stv /\
    type_memory_bytes cenv sty < dimword (:256)
Proof
  rpt strip_tac >>
  drule expr_body_pre_type_evaluates >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  drule_all expr_body_pre_copy_ok >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  metis_tac[widening_memory_layout_bound]
QED
