Theory bodyPtrBopCases
Ancestors
  bodyPtrBopPairCompose bodyPtrBopOperandContract bodyPtrBopScalarOutcome bodyPtrBopClassification
  exprBopLowering exprSimOperators exprSimWordArgs exprBopSimProps exprSimSource
  bodyPtrPreds bodyPtrDefs exprSimHypsDefs bodyPtrBopTypedBytes

Theorem bop_word_pair_sim_ptr:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  body_exprs_ptr_ok cx [e1;e2] /\ bop <> In /\ bop <> NotIn /\
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) ==>
  expr_sim_ptr d ctx PG func cenv cx ty (Builtin ann (Bop bop) [e1;e2]) es
Proof
  strip_tac >> simp[expr_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  `~(is_bytestring_type (expr_type e1) /\ (bop = Eq \/ bop = NotEq))` by
    metis_tac[bop_machine_word_not_bytestring] >>
  `~((bop = In \/ bop = NotIn) /\ is_ArrayT (expr_type e2))` by simp[] >>
  drule_all lower_value_bop >> strip_tac >>
  drule expr_body_pre_bop >> strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env e2 es` by metis_tac[] >>
  `is_word_type (expr_type e1) /\ is_word_type (expr_type e2)` by
    metis_tac[word_value_type_word] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  rev_drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  drule compile_binop_shape >> strip_tac >>
  pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
  irule (REWRITE_RULE [bop_operand_post_def,
    loweringPostsTheory.post_value_type_def] bop_word_pair_outcome_ptr) >>
  simp[bop_operand_entry_def] >>
  reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [`s1`, `s2`, `expr_type e1`, `expr_type e1`, `x`, `y`] >> simp[]
QED
