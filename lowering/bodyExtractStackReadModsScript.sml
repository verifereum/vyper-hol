(* Extract32 returns a materialized stack word. *)
Theory bodyExtractStackReadMods
Ancestors
  bodyAggregateReadMods bodyAggregateReadPostMods bodyFullPostsMods
  bodyFullShared gasShadowCompileStmtHelpers gasShadowState
  typeBuiltinPrereqs exprSimConvert exprLowering compileEnv loweringPosts
  vyperAST vyperInterpreter vyperState

val extract_expr = ``TypeBuiltin (BaseT bt) Extract32 (BaseT bt) [src;off]``;

Theorem extract32_stack_read_cuts[local]:
  lower_value compile_expr cenv ty ^extract_expr sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^extract_expr)
    shadow_sa = (op,shadow_sb) /\ gas_shadow_state sa shadow_sa ==>
  compile_expr cenv ty ^extract_expr sa = (StackValue (BaseT bt) op,sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^extract_expr)
    shadow_sa = (StackValue (BaseT bt) op,shadow_sb)
Proof
  strip_tac >>
  Cases_on `compile_expr cenv ty ^extract_expr sa` >>
  rename1 `_ = (vv,real_end)` >>
  drule_then strip_assume_tac extract32_compile_equations >>
  qpat_x_assum `vv = StackValue _ _` SUBST_ALL_TAC >>
  Cases_on `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^extract_expr) shadow_sa` >>
  rename1 `_ = (shadow_vv,shadow_end)` >>
  `gas_shadow_compiles (compile_expr cenv ty ^extract_expr)
     (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^extract_expr))` by
    MATCH_ACCEPT_TAC gas_shadow_stmt_compile_expr_env >>
  drule_all_then strip_assume_tac gas_shadow_step >>
  qpat_x_assum `shadow_vv = _` SUBST_ALL_TAC >>
  qpat_x_assum `lower_value _ _ _ (TypeBuiltin _ _ _ _) _ = _` mp_tac >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[lower_value_def,comp_bind_def,unwrap_value_def,comp_return_def] >>
  rpt strip_tac >> simp[]
QED

Theorem extract32_stack_read_from_vv_mods:
  is_word_type (BaseT bt) /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty ^extract_expr es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty ^extract_expr es
Proof
  strip_tac >> irule materialized_value_from_vv_mods >>
  qpat_assum `expr_vv_sim_full_mods _ _ _ _ _ _` (irule_at Any) >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_then ACCEPT_TAC eval_expr_type_builtin_value) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac extract32_stack_read_cuts >>
  qexists_tac `StackValue (BaseT bt) op` >> asm_rewrite_tac[] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `raw = Value _` SUBST_ALL_TAC >>
  `~is_word_type (post_value_type cenv ^extract_expr) ==>
     ptr_buf_ok cenv ^extract_expr op G t` by simp[post_value_type_def,expr_type_def] >>
  drule_all_then strip_assume_tac stack_value_read_post_mods >> asm_rewrite_tac[]
QED
