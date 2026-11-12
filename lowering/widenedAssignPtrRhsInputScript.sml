(* Physical RHS layout is recovered from the actual post, not buffer capacity. *)
Theory widenedAssignPtrRhsInput
Ancestors exprSimHyps exprSimHypsDefs exprOperandVar bodyPtrDefs loweringPosts exprSimProps
  compileEnv valueEncoding valueEncodingDefs venomExecSemantics venomState
  ptrDiscipline finite_map words

Theorem retained_rhs_physical_input_ptr:
  !ce cx env e es ctx fn sa sb s0 ee v op s G tn ty.
    expr_body_pre ce cx env e es /\
    expr_post ctx fn ce cx e es sa sb s0 ee v op s /\
    ~is_word_type (post_value_type ce e) /\
    lower_value compile_expr ce ty e sa = (op,sb) /\
    local_ptrs_reserved ce sa /\
    ptr_val_ok cx (post_value_type ce e) v op G tn s /\
    ptr_buf_ok ce e op G s ==>
    ?tv w.
      evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tv /\
      type_memory_bytes ce (post_value_type ce e) = type_memory_size tv /\
      val_wf tv v /\ eval_operand op s = SOME w /\
      op_taint tn op = {} /\
      expr_val_at ce cx (post_value_type ce e) sa sb ee v op s /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory tv v (w2n w) m) /\
      (type_memory_bytes ce (lowered_value_type ce e) = 0 \/
       ?src. op = Var src /\ lookup_var src s = SOME w /\
         not_fresh_at sb src /\
         ptr_covers G tn src s (type_memory_bytes ce (lowered_value_type ce e)))
Proof
  rpt gen_tac >> strip_tac >>
  drule post_type_evaluates >> strip_tac >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `type_memory_bytes ce (post_value_type ce e) = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `expr_val_at ce cx (post_value_type ce e) sa sb ee v op s` by
    fs[expr_post_def] >>
  `val_wf tv v /\ ?w. eval_operand op s = SOME w` by
    (fs[expr_val_at_def] >> metis_tac[]) >>
  qexistsl_tac [`tv`,`w`] >> simp[] >>
  `op_taint tn op = {} /\
   (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
     val_in_memory tv v (w2n w) m)` by
    (fs[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]) >>
  simp[] >>
  Cases_on `type_memory_bytes ce (lowered_value_type ce e) = 0` >> simp[] >>
  drule compile_lower_value_var >> disch_then drule >> disch_tac >>
  fs[ptr_buf_ok_def] >> first_x_assum drule >> simp[] >> strip_tac >>
  gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]
QED
