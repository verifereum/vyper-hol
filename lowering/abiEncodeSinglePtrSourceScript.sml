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
