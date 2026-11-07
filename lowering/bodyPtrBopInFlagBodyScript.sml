Theory bodyPtrBopInFlagBody
Ancestors bodyPtrBopInFlagCompose bodyPtrBopInFlagInterface
  bodyPtrBopOperandContract bodyPtrBopEntry exprBopLowering
  exprSimOperators exprSimWordArgs exprBopSimProps exprSimSource
  bodyPtrPreds bodyPtrDefs exprSimHypsDefs exprLoweringProps
  compileEnv exprPtrUnwrap vyperAST vyperTypeSystem

Theorem membership_flag_pair_sim_ptr:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  body_exprs_ptr_ok cx [e1;e2] /\ (bop = In \/ bop = NotIn) /\
  is_word_type (expr_type e1) /\ expr_type e2 = FlagT fid ==>
  expr_sim_ptr d ctx PG func cenv cx ty (Builtin ann (Bop bop) [e1;e2]) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[expr_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  `~(is_bytestring_type (expr_type e1) /\ (bop = Eq \/ bop = NotEq)) /\
   ~((bop = In \/ bop = NotIn) /\ is_ArrayT (expr_type e2))` by
    (Cases_on `bop` >> gvs[]) >>
  drule_all lower_value_bop >> strip_tac >>
  drule expr_body_pre_bop >> strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env e2 es` by metis_tac[] >>
  `is_word_type (expr_type e2)` by simp[is_word_type_def] >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  rev_drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  drule compile_binop_shape >> strip_tac >>
  pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
  irule (REWRITE_RULE [bop_operand_post_def] membership_flag_pair_outcome_ptr) >>
  simp[bop_operand_entry_def] >>
  reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [`s1`, `s2`, `expr_type e1`, `expr_type e1`, `x`, `y`] >> simp[]
QED

Theorem membership_flag_ptr_ok:
  !cx ann bop e1 e2 fid.
    (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) /\
    expr_type e2 = FlagT fid /\ body_exprs_ptr_ok cx [e1;e2] ==>
    body_expr_ptr_ok cx (Builtin ann (Bop bop) [e1;e2])
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[body_expr_ptr_ok_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_ptr d ctx PG func cenv cx ty (Builtin ann (Bop bop) [e1;e2]) es` by
    (irule membership_flag_pair_sim_ptr >> simp[] >> metis_tac[]) >> simp[] >>
  irule expr_vv_sim_ptr_stack >> simp[compile_bop_stack] >>
  metis_tac[eval_expr_builtin_value]
QED
