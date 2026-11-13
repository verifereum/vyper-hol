Theory bodyFullBuiltinEnvHash
Ancestors
  bodyFullExprGeneric bodyFullPreds bodySimFull exprSimSource exprSimHypsDefs
  exprLowering exprLoweringProps exprBopLowering valueEncoding builtinProps builtinSimple vyperTypeSystem
  gasShadowCompileStmtHelpers gasShadowState
  compileEnv vyperAST list pair

Theorem hash_builtin_full_vv:
  (bt = BlockHash \/ bt = BlobHash) /\
  expr_body_pre cenv cx env (Builtin a bt args) es /\
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin a bt args) es ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin a bt args) es
Proof
  rpt strip_tac >>
  `a = BaseT (BytesT (Fixed 32))` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  `!bt args. names_builtin bt args ==> bt <> BlockHash /\ bt <> BlobHash` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `~names_builtin bt args` by metis_tac[] >>
  irule expr_vv_sim_stack_full >>
  simp[expr_type_def, is_word_type_def] >>
  (conj_tac
   >- (gen_tac >>
       gvs[compile_expr_builtin_dispatch, names_builtin_def] >>
       simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
            compile_builtin_dispatch_body_def, as_stack_val_pair,
            pairTheory.UNCURRY])) >>
  rpt strip_tac >> irule exprLoweringPropsTheory.eval_expr_builtin_value >>
  goal_assum (drule_at Any)
QED
