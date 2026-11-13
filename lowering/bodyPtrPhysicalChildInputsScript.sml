(* Checked physical inputs for an aggregate literal child store. *)
Theory bodyPtrPhysicalChildInputs
Ancestors
  exprSimAggregateChildren exprSimHyps exprSimHypsDefs loweringPosts
  bodyPtrDefs compileEnv loweringStateRelDefs vyperState vyperTypeSystem
  valueEncoding valueEncodingProps valueEncodingDefs venomState ptrDiscipline
  assignBasePtrBoundary finite_map words list

Theorem literal_physical_source_inputs:
  expr_body_pre ce cx env e esi /\
  bind (eval_expr cx e) (read_result cx) esi = (INL v,es') /\
  expr_post ctx func ce cx e ers sa sb s0 es' v op s /\
  post_value_type ce e = lowered_value_type ce e /\
  ~is_word_type (post_value_type ce e) /\
  ptr_val_ok cx (post_value_type ce e) v op G tn s /\
  ptr_buf_ok ce e op G s ==>
  ?stv sw.
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    value_has_type stv v /\ val_wf stv v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
    type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e) /\
    eval_operand op s = SOME sw /\ op_taint tn op = {} /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n sw) m) /\
    (0 < type_memory_size stv ==>
      ?src. op = Var src /\ ptr_covers G tn src s (type_memory_size stv))
Proof
  strip_tac >>
  drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) aggregate_child_physical_encoding) >>
  strip_tac >>
  qpat_x_assum `post_value_type ce e = lowered_value_type ce e` SUBST_ALL_TAC >>
  `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv` by
    (irule expr_sim_inv_memory_size >>
     fs[expr_body_pre_def] >> metis_tac[]) >>
  qexistsl_tac [`stv`, `sw`] >> asm_simp_tac std_ss [] >>
  conj_tac >- fs[ptr_val_ok_def] >>
  conj_tac >- (fs[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]) >>
  strip_tac >> irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >>
  fs[ptr_val_ok_def] >> qexistsl_tac [`ce`, `e`] >> asm_simp_tac std_ss []
QED
