(* Full destination capacity at an allocated unwrap endpoint. *)
Theory bodyUnwrapCapacity
Ancestors
  exprSimMemDefs exprSimUnwrapProps fragGasPathMem valueEncodingProps context exprSimProps

Theorem unwrap_expr_post_capacity:
  ~is_word_type (expr_type e) /\
  expr_post ctx func cenv cx e es sa sb s0 ee v op s /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  eval_operand op s = SOME w /\
  w2n w + type_memory_size tv <= s.vs_alloca_next ==>
  vv_store_bound cx (expr_type e) (expr_type e) ee (Value v)
    (LocatedValue (expr_type e) (mk_ptr op LocMemory)) s
Proof
  strip_tac >>
  `expr_store_bound cx (expr_type e) v op s` by
    (irule expr_store_bound_capacity >> simp[] >> metis_tac[]) >>
  simp[vv_store_bound_def, mk_ptr_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  `val_wf tv v` by
    fs[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_at_def] >>
  drule val_store_size_le >> decide_tac
QED
