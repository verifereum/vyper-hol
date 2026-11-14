(* Joint hash execution: the argument's value judgment, followed by the
   hash suffix, with one endpoint before all valid storage horizons. *)
Theory bodyFullHash
Ancestors
  bodyFullHashKeccak bodyFullHashSha
  bodyFullOfVV bodyFullPreds bodySimFull
  exprSimHyps exprSimHypsDefs exprSimSource
  bodyPtrHashBuiltinsCases gasShadowCompile gasShadowState
  loweringPosts exprLowering exprLoweringProps compileEnv valueEncoding
  vyperTyping vyperTypeSystem vyperInterpreter vyperState vyperAST

val _ = Parse.hide "body";

(* The singleton lowering uses lower_value at expr_type e. The argument
   judgment already includes its memory read. The hash suffix adds zero
   explicit source GAS observations, including SHA256's internal GAS. *)
Theorem hash_vv_sim_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx env ty ann bt e es.
    (bt = Keccak256 \/ bt = Sha256) /\
    expr_body_pre cenv cx env (Builtin ann bt [e]) es /\
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (expr_type e) e es ==>
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann bt [e]) es
Proof
  metis_tac[keccak_vv_sim_full, sha_vv_sim_full]
QED

Theorem hash_expr_full_ok:
  !cx ty bt es.
    (bt = Keccak256 \/ bt = Sha256) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (Builtin ty bt es)
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  rewrite_tac[body_expr_full_ok_def] >>
  reverse conj_tac >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  `LENGTH es = 1` by metis_tac[hash_body_pre_arity] >>
  `?e. es = [e]` by (Cases_on `es` >> gvs[listTheory.LENGTH_EQ_NUM]) >>
  qpat_x_assum `es = [e]` SUBST_ALL_TAC >>
  `builtin_args_length_ok bt 1` by
    (qpat_assum `bt = Keccak256 \/ bt = Sha256` strip_assume_tac >>
     gvs[vyperContextTheory.builtin_args_length_ok_def]) >>
  `body_expr_full_ok cx e` by
    (qpat_x_assum `builtin_args_length_ok _ _ ==> body_exprs_full_ok _ _` mp_tac >>
     simp[body_exprs_full_ok_def]) >>
  `expr_body_pre cenv cx env e es'` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >>
     gvs[expr_body_pre_def]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es'` by
    (gvs[body_expr_full_ok_def] >> metis_tac[]) >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty' (Builtin ty bt [e]) es'` by
    (irule hash_vv_sim_full >> metis_tac[]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule expr_sim_full_of_vv >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> simp[]) >>
  qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _`
    (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  qexists_tac `x` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (Builtin ty bt [e])
    (es' with gas_obs := gs)` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
  strip_tac >> gvs[] >> metis_tac[]
QED
