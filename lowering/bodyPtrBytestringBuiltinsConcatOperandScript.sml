(* Concat reads scalar byte operands at their source annotation, including
   internal calls: post_value_type keeps word and bytestring annotations. *)
Theory bodyPtrBytestringBuiltinsConcatOperand
Ancestors
  bodyPtrDefs loweringPosts representationCleanPtr
  vyperAST vyperValue vyperContext compileEnv vyperTypeSystem vyperTyping
  exprLowering valueEncoding compileEnv words list venomState

Theorem concat_operand_bytes_read:
  expr_post ctx fn ce cx e es sa sb s0 ee v op s /\
  ptr_val_ok cx (post_value_type ce e) v op G tn s /\
  is_bytestring_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v ==>
  ?w p. op = Var p /\ lookup_var p s = SOME w /\
    ptr_covers G tn p s
      (32 + LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => [])) /\
    (!i. w2n w <= i /\
      i < w2n w + 32 + LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) ==>
      i NOTIN tn.t_mem) /\
    LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) < dimword (:256) /\
    w2n w + 32 + LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) <= dimword (:256) /\
    w2n w + 32 < dimword (:256) /\
    mem_word_at (w2n w) s.vs_memory = n2w (LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => [])) /\
    mem_bytes_at (w2n w + 32) (LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => [])) s.vs_memory =
      (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) /\
    LENGTH (case v of BytesV bs => bs | StringV str => MAP (n2w o ORD) str | _ => []) <= concat_payload_capacity (expr_type e)
Proof
  strip_tac >>
  `post_value_type ce e = expr_type e` by simp[] >>
  `stmt_state_rel ctx fn ce cx ee s /\
   expr_val_at ce cx (expr_type e) sa sb ee v op s /\
   expr_val_rel cx (expr_type e) v op s` by fs[expr_post_def] >>
  `?w. eval_operand op s = SOME w` by fs[expr_val_rel_def] >>
  `!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ 32 <= val_footprint tv v ==>
    w2n w+32 < dimword (:256)` by
    (rpt strip_tac >>
     drule exprSimPropsTheory.stmt_state_rel_region_lt >> strip_tac >>
     gvs[expr_val_at_def] >> res_tac >> decide_tac) >>
  Cases_on `expr_type e` >> gvs[is_bytestring_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def]
  >~ [`BytesT bd`]
  >- (Cases_on `bd` >> gvs[is_bytestring_type_def, evaluate_type_def] >>
      Cases_on `v` >> gvs[value_has_type_def] >>
      drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`) expr_val_at_raw_return_resources >>
      gvs[is_word_type_def, evaluate_type_def, val_footprint_def,
          expr_val_rel_def, val_in_memory_def, concat_payload_capacity_def,
          eval_operand_def] >>
      metis_tac[]) >>
  gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def] >>
  drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`) expr_val_at_raw_return_resources >>
  gvs[is_word_type_def, evaluate_type_def, val_footprint_def,
          expr_val_rel_def, val_in_memory_def, concat_payload_capacity_def,
          eval_operand_def] >> metis_tac[]
QED
