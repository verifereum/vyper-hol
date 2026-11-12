(* Caller-side source boundary for the single-argument encoder. *)
Theory abiEncodeSinglePtrSource
Ancestors
  abiEncodeMaterialize abiEncoderSourceRobust bodyPtrDefs
  exprSimProps exprSimHyps exprSimDefs
  valueCopyBytes valueEncodingTyping loweringPosts compileEnv
  exprSimIfExpWidenedPhysicalType abiEncodeOwnership
  representationCleanPtr

Theorem abi_encode_nonword_robust_lowered_source:
  expr_body_pre ce cx env e es /\
  expr_post ctx func ce cx e es0 sa sb s0 ee v src s /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\
  ptr_val_ok cx (post_value_type ce e) v src G tn s ==>
  ?w. eval_operand src s = SOME w /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem)
Proof
  strip_tac >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[post_value_type_nonword] >>
  `?ptv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv` by
    (`post_value_type ce e = expr_type e \/
      post_value_type ce e = lowered_value_type ce e` by
      (Cases_on `e` >> simp[post_value_type_def] >>
       rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
       simp[post_value_type_def, vyperASTTheory.expr_type_def] >>
       IF_CASES_TAC >> simp[]) >>
     metis_tac[expr_body_pre_type_evaluates, optionTheory.IS_SOME_EXISTS]) >>
  `?w. eval_operand src s = SOME w` by
    (fs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory ptv v (w2n w) mem` by
    (fs[ptr_val_ok_def, ptr_mem_ok_def] >> metis_tac[]) >>
  qexists `w` >> simp[] >>
  Cases_on `post_value_type ce e = lowered_value_type ce e`
  >- gvs[] >>
  drule_all materialize_post_lowered_classify >> simp[] >> strip_tac >>
  rpt strip_tac >> irule bytestring_val_in_memory_transfer >> simp[] >>
  qexistsl [`post_value_type ce e`, `lowered_value_type ce e`,
    `get_tenv cx`, `ptv`] >> simp[]
QED

Theorem abi_encode_nonword_source_resources:
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,ee) /\
  expr_post ctx func ce cx e ers sa sb r ee v src s /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  value_has_type tv v /\
  ptr_val_ok cx (post_value_type ce e) v src G tn s ==>
  ?w. eval_operand src s = SOME w /\ op_taint tn src = {} /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem) /\
    (0 < val_footprint tv v ==>
      (?x. src = Var x /\ ptr_covers G tn x s (val_footprint tv v)) /\
      w2n w + val_footprint tv v <= s.vs_alloca_next)
Proof
  strip_tac >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[post_value_type_nonword] >>
  drule_all exprSimAggregateChildrenTheory.aggregate_child_physical_encoding >>
  strip_tac >>
  `val_footprint stv v = val_footprint tv v` by
    (Cases_on `post_value_type ce e = lowered_value_type ce e`
     >- gvs[] >>
     `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
       metis_tac[expr_body_pre_lowered_fits] >>
     drule_all materialize_post_lowered_classify >> simp[] >> strip_tac >>
     irule bytestring_val_footprint_eq >> metis_tac[]) >>
  drule_all abi_encode_nonword_robust_lowered_source >> strip_tac >>
  qexists `w` >> simp[] >>
  conj_tac >- fs[ptr_val_ok_def] >> strip_tac >> conj_tac
  >- (`val_footprint stv v <> 0` by decide_tac >>
      irule ptr_val_ok_read_covers >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  `val_footprint stv v = 0 \/
   w2n w + val_footprint stv v <= s.vs_alloca_next` by
    (irule abi_encode_owned_footprint_frontier >>
     fs[expr_post_def] >> metis_tac[]) >>
  gvs[]
QED
