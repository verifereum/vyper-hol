(* Joint AnnAssign: physical layout of a widened aggregate RHS. *)
Theory bodyFullAnnAssignWidened
Ancestors
  assignRelayoutCaller annassignRelayoutSource annassignRelayoutFrag annassignRelayoutPost
  bodySimFull bodyPtrDefs exprSimSource exprSimHypsDefs
  loweringPosts exprLoweringProps exprOperandVar assignBasePtrBoundary
  externalReturnBounds exprSimAggregateChildren representationCleanPtr
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

(* The strict physical layout supplies a real pointer variable and robust
   source encoding; the declaration's reserved allocation is disjoint. *)
Theorem annassign_widened_full_source:
  expr_post H ctx func ce cx e es sa sb s0 mid v op s /\
  post_value_type ce e = sty /\ sty <> expr_type e /\
  type_widens_to (get_tenv cx) sty (expr_type e) /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ ~is_word_type sty /\
  val_footprint stv v = type_memory_size stv /\ 0 < type_memory_size stv /\
  ptr_val_ok cx sty v op G tn s /\
  FLOOKUP s0.vs_allocas aid = SOME (w2n dw,sz) /\ aid < sa.cs_next_id /\
  type_memory_size dtv <= sz /\ not_fresh_at sa p /\ lookup_var p s0 = SOME dw ==>
  ?xs sw.
    op = Var xs /\ lookup_var xs s = SOME sw /\ lookup_var p s = SOME dw /\
    FLOOKUP s.vs_allocas aid = SOME (w2n dw,sz) /\
    ptr_covers G tn xs s (type_memory_size stv) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory stv v (w2n sw) mem) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    w2n sw + type_memory_size stv <= s.vs_alloca_next /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw) /\
    expr_val_at ce cx sty sa sb mid v (Var xs) s
Proof
  strip_tac >>
  `?sw. eval_operand op s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\ lookup_var p s = SOME dw /\
    FLOOKUP s.vs_allocas aid = SOME (w2n dw,sz) /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n dw + type_memory_size dtv < dimword (:256) /\
    (w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw)` by
    (irule expr_post_reserved_destination_source >> simp[] >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[]) >>
  `expr_val_at ce cx sty sa sb mid v op s /\
   stmt_state_rel H ctx func ce cx mid s` by fs[expr_post_def] >>
  `?xs. op = Var xs /\ ptr_covers G tn xs s (type_memory_size stv)` by
    (irule ptr_val_ok_read_covers >> simp[] >>
     goal_assum (drule_at (Pat `ptr_val_ok _ _ _ _ _ _ _`)) >> simp[]) >>
  `w2n sw + type_memory_size stv <= s.vs_alloca_next` by
    (drule_all expr_val_at_frontier >> strip_tac >> gvs[]) >>
  qexistsl_tac [`xs`, `sw`] >> gvs[venomStateTheory.eval_operand_def] >>
  fs[ptr_val_ok_def, ptr_mem_ok_def, venomStateTheory.eval_operand_def] >>
  metis_tac[]
QED
