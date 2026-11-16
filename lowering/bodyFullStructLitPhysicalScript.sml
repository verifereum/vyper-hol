(* Source-side physical layout resources for the joint StructLit case. *)
Theory bodyFullStructLitPhysical
Ancestors
  immutableDeployPhysicalSource bodyPtrDefs
  loweringPosts valueCopyBytes
Libs monadsyntax

Theorem structlit_child_physical_robust:
  expr_body_pre ce cx env e es /\
  (do pv <- eval_expr cx e; read_result cx pv od) es = (INL v,ee) /\
  expr_post H ctx func ce cx e es sa sb s0 ee v op s /\
  ptr_val_ok cx (post_value_type ce e) v op G tn s /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
  ~is_word_type (lowered_value_type ce e) ==>
  ?w. eval_operand op s = SOME w /\
      !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
            val_in_memory stv v (w2n w) mem
Proof
  strip_tac >>
  drule_all immutable_rhs_physical_typed >> strip_tac >> gvs[] >>
  drule_all immutable_rhs_physical_memory >> strip_tac >>
  drule immutable_rhs_post_physical_classify >> strip_tac
  >- (gvs[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]) >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[is_bytestring_word_type] >>
  qexists_tac `w` >> simp[] >> rpt strip_tac >>
  `val_in_memory ptv v (w2n w) mem` by
    metis_tac[ptr_val_ok_def, ptr_mem_ok_def] >>
  metis_tac[bytestring_val_in_memory_transfer]
QED
