Theory bodyFullBuiltinEnvHash
Ancestors
  bodyFullBuiltinEnvHashCompose bodyFullBuiltinEnvBlockHashSuffix
  bodyFullBuiltinEnvBlobHashSuffix
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

Theorem hash_builtin_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (bt = BlockHash \/ bt = BlobHash) /\
    builtin_args_length_ok bt (LENGTH args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt <> Len ==>
     body_exprs_full_ok cx args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt = Len ==>
     body_expr_full_ok cx (HD args)) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >> strip_tac >>
  `body_exprs_full_ok cx args` by
    (Cases_on `bt = BlockHash` >> gvs[]) >>
  (conj_asm1_tac
   >- (mp_tac hash_builtin_value_from_suffixes >>
       (impl_tac >- (conj_tac >- ACCEPT_TAC blockhash_full_suffix >>
                     (rpt gen_tac >> MATCH_ACCEPT_TAC blobhash_full_suffix))) >>
       disch_then irule >> metis_tac[]) >>
   metis_tac[hash_builtin_full_vv])
QED
