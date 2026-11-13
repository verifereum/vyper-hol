Theory bodyPtrIfExpNoCopyAlignment
Ancestors
  bodyPtrIfExpNoCopy vyperTypeSystem exprSimHypsDefs bodyPtrDefs

(* Arm judgments already express pointer interpretation at the annotation,
   not at lowered_value_type. IfExp typing makes that annotation precisely
   the result type. Lowered-type differences affect buffer capacity only. *)
Theorem ifexp_no_copy_arm_post:
  !ce cx env es ty cond a b arm v op G tn s.
    expr_body_pre ce cx env (IfExp ty cond a b) es /\
    (arm = a \/ arm = b) /\
    ~is_word_type ty /\
    same_memory_layout ce (lowered_value_type ce arm) ty /\
    ptr_val_ok cx (expr_type arm) v op G tn s /\
    ptr_buf_ok ce arm op G s ==>
    ptr_mem_ok cx ty v op G tn s /\
    ptr_buf_ok ce (IfExp ty cond a b) op G s
Proof
  rpt strip_tac >>
  `expr_type arm = ty` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  gvs[ptr_val_ok_def] >>
  irule ifexp_no_copy_capacity >>
  goal_assum (drule_at Any) >>
  simp[exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def]
QED
