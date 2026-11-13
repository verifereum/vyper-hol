Theory bodyPtrTypeBuiltinsMemoryOperandResources
Ancestors
  bodyPtrDefs loweringPosts bodyPtrSignedConvertHeaderLoad
  assignBasePtrBoundary exprLoweringProps venomState

(* Common memory operand interface: retain the post's actual type explicitly. *)
Theorem convert_memory_operand_resources:
  expr_post ctx fn cenv cx e es ca sa s0 ee v op s /\
  post_value_type cenv e = expr_type e /\ ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn s /\
  ptr_buf_ok cenv e op G s /\ 0 < type_memory_bytes cenv (lowered_value_type cenv e) ==>
  ?src a. op = Var src /\ lookup_var src s = SOME a /\
    stmt_state_rel ctx fn cenv cx ee s /\
    expr_val_at cenv cx (expr_type e) ca sa ee v (Var src) s /\
    op_taint tn (Var src) = {} /\
    ptr_covers G tn src s (type_memory_bytes cenv (lowered_value_type cenv e)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v (w2n a) m)
Proof
  strip_tac >>
  `?w. eval_operand op s = SOME w` by
    (fs[expr_post_def, expr_val_rel_def]) >>
  `op_taint tn op = {}` by fs[ptr_val_ok_def] >>
  `?p. op = Var p /\ ptr_covers G tn p s
    (type_memory_bytes cenv (lowered_value_type cenv e))` by
    (irule ptr_buf_ok_read_covers >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  qexistsl_tac [`p`,`w`] >>
  fs[eval_operand_def, expr_post_def, ptr_val_ok_def, ptr_mem_ok_def]
QED
