(* Joint AnnAssign: physical layout of a widened aggregate RHS. *)
Theory bodyFullAnnAssignWidened
Ancestors
  assignRelayoutCaller annassignRelayoutSource annassignRelayoutFrag annassignRelayoutPost
  bodySimFull bodyPtrDefs exprSimSource exprSimHypsDefs
  loweringPosts exprLoweringProps exprOperandVar assignBasePtrBoundary
  externalReturnBounds exprSimAggregateChildren
  vyperTypeSystem vyperTypeInvariants vyperInterpreter vyperState
  compileEnv venomState venomMemDefs words arithmetic

Theorem annassign_widened_full_layout:
  expr_body_pre ce cx env e es /\
  type_widens_to env.type_defs (expr_type e) typ /\ ~is_word_type typ /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  type_memory_bytes ce typ < 2 ** 64 /\
  supported_expr tops e /\ ce.ce_func_return_type = build_func_return_type tops /\
  supported_program tops /\ get_module_code cx NONE = SOME tops ==>
  ?stv.
    ~is_bytestring_type typ /\
    ~is_word_type (lowered_value_type ce e) /\
    ~is_bytestring_type (lowered_value_type ce e) /\
    post_value_type ce e = lowered_value_type ce e /\
    lowered_value_type ce e <> expr_type e /\ lowered_value_type ce e <> typ /\
    type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e) /\
    type_widens_to (get_tenv cx) (lowered_value_type ce e) typ /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
    type_memory_bytes ce typ = type_memory_size tyv /\
    type_memory_size stv <= type_memory_size tyv /\
    0 < type_memory_size stv /\ type_memory_size stv < dimword (:256) /\
    (!gs v mid. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gs) = (INL v,mid) ==>
      value_has_type stv v /\ value_has_type tyv v /\
      val_wf stv v /\ val_wf tyv v /\
      val_footprint stv v = type_memory_size stv)
Proof
  strip_tac >> drule_all assign_relayout_source_classify >> strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  drule_all widening_memory_layout_bound >> strip_tac >>
  `0 < type_memory_size stv` by
    (irule strict_widening_source_positive >> metis_tac[]) >>
  qexists_tac `stv` >> simp[] >> rpt strip_tac >>
  metis_tac[annassign_relayout_read_layout]
QED
