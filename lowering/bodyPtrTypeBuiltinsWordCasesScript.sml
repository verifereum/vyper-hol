Theory bodyPtrTypeBuiltinsWordCases
Ancestors wordArgsPtr
  bodyPtrDefs bodyPtrTypeBuiltinsBoundWords
  bodyPtrTypeBuiltinsEmptyWord bodyPtrSignedConvertLiteralPost
  bodyPtrTypeBuiltinsPure stmtFragPtr bodyPtrPreds exprPtrUnwrap
  exprSimSource exprSimHypsDefs exprLoweringProps vyperAST exprLowering compileEnv exprSimConvert exprSimHyps vyperTypeSystem vyperTypeCallGraph

Theorem bound_builtin_expr_sim_ptr:
  !d ctx PG func cenv cx env ty ann tb typ args es.
    MEM tb [MaxValue;MinValue;Epsilon] /\
    expr_sim_pre cenv cx env (TypeBuiltin ann tb typ args) es ==>
    expr_sim_ptr d ctx PG func cenv cx ty (TypeBuiltin ann tb typ args) es
Proof
  rpt gen_tac >> strip_tac >> rw[expr_sim_ptr_def] >>
  drule_all bound_builtin_source_gas >> strip_tac >>
  drule_all bound_builtin_typed_literal >> strip_tac >> gvs[] >>
  irule gas_outcome_ptr_pure >> simp[] >>
  simp[expr_type_def, ghost_inv_gas_obs, wordArgsPtrTheory.ghost_kept_refl, ptr_val_ok_word_literal] >>
  irule expr_post_initial_literal >> simp[expr_type_def]
QED

Theorem empty_word_expr_sim_ptr:
  !d ctx PG func cenv cx env ty ann typ args es.
    is_word_type typ /\
    expr_sim_pre cenv cx env (TypeBuiltin ann Empty typ args) es ==>
    expr_sim_ptr d ctx PG func cenv cx ty (TypeBuiltin ann Empty typ args) es
Proof
  rpt gen_tac >> strip_tac >> rw[expr_sim_ptr_def] >>
  drule_all empty_source_gas >> strip_tac >>
  drule_all empty_word_typed_literal >> strip_tac >> gvs[] >>
  irule gas_outcome_ptr_pure >> simp[] >>
  simp[expr_type_def, ghost_inv_gas_obs, wordArgsPtrTheory.ghost_kept_refl, ptr_val_ok_word_literal] >>
  irule expr_post_initial_literal >> simp[expr_type_def]
QED

Theorem bound_builtin_stack_shape:
  !cenv ty ann tb typ args sa.
    MEM tb [MaxValue;MinValue;Epsilon] ==>
    ?t op sb. compile_expr cenv ty (TypeBuiltin ann tb typ args) sa =
      (StackValue t op,sb)
Proof
  rw[] >> simp[Once compile_expr_def, compile_expr_type_builtin_dispatch, comp_return_def] >>
  Cases_on `type_bounds typ` >> simp[]
QED

Theorem empty_word_stack_shape:
  !cenv ty ann typ args sa.
    is_word_type typ ==>
    ?t op sb. compile_expr cenv ty (TypeBuiltin ann Empty typ args) sa =
      (StackValue t op,sb)
Proof
  rpt strip_tac >> simp[Once compile_expr_def, compile_expr_type_builtin_dispatch, comp_return_def]
QED

Theorem bound_builtin_body_pre:
  !cenv cx env ann tb typ args es.
    MEM tb [MaxValue;MinValue;Epsilon] /\
    expr_body_pre cenv cx env (TypeBuiltin ann tb typ args) es ==>
    expr_sim_pre cenv cx env (TypeBuiltin ann tb typ args) es
Proof
  rpt gen_tac >> strip_tac >>
  `args = []` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_type_builtin_args_def] >>
  gvs[expr_sim_pre_body, int_calls_expr_def]
QED

Theorem empty_body_pre:
  !cenv cx env ann typ args es.
    expr_body_pre cenv cx env (TypeBuiltin ann Empty typ args) es ==>
    expr_sim_pre cenv cx env (TypeBuiltin ann Empty typ args) es
Proof
  rpt gen_tac >> strip_tac >>
  `args = []` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_type_builtin_args_def] >>
  gvs[expr_sim_pre_body, int_calls_expr_def]
QED

Theorem bound_builtin_body_expr_ptr_ok:
  !cx ann tb typ args.
    MEM tb [MaxValue;MinValue;Epsilon] ==>
    body_expr_ptr_ok cx (TypeBuiltin ann tb typ args)
Proof
  rpt gen_tac >> strip_tac >> rw[body_expr_ptr_ok_def] >>
  drule_all bound_builtin_body_pre >> strip_tac >>
  `expr_sim_ptr d ctx PG func cenv cx ty (TypeBuiltin ann tb typ args) es` by
    (irule bound_builtin_expr_sim_ptr >> metis_tac[]) >>
  simp[] >> irule expr_vv_sim_ptr_stack >> simp[] >>
  conj_tac
  >- (gen_tac >> irule bound_builtin_stack_shape >> simp[]) >>
  metis_tac[eval_expr_type_builtin_value]
QED

Theorem empty_word_body_expr_ptr_ok:
  !cx ann typ args.
    is_word_type typ ==>
    body_expr_ptr_ok cx (TypeBuiltin ann Empty typ args)
Proof
  rpt gen_tac >> strip_tac >> rw[body_expr_ptr_ok_def] >>
  drule_all empty_body_pre >> strip_tac >>
  `expr_sim_ptr d ctx PG func cenv cx ty (TypeBuiltin ann Empty typ args) es` by
    (irule empty_word_expr_sim_ptr >> metis_tac[]) >>
  simp[] >> irule expr_vv_sim_ptr_stack >> simp[] >>
  conj_tac
  >- (gen_tac >> irule empty_word_stack_shape >> simp[]) >>
  metis_tac[eval_expr_type_builtin_value]
QED
