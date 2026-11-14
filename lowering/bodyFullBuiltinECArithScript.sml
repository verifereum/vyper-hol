(* Full EC arithmetic simulation at arbitrary (DF,lo). The two operands
   precede the fresh input/output buffers; their full judgments supply the
   single execution used by the staging prefix and precompile suffix.
   The fixed uint256[2] result allows the full vv-to-value adapter. *)
Theory bodyFullBuiltinECArith
Ancestors
  bodyFullExprGeneric bodyFullPreds bodySimFull bodyFullOfVV
  exprSimECArith bodyMemEcArithOperands bodyFullAllocaFresh
  bodyFullAllocGeneric bodyFullUnwrapRun bodyFullGhostFrame wordArgsPtr
  bodyFullBuiltinPrecompileSuffixPath bodyFullBuiltinPrecompileSuffixAbort
  bodyFullBuiltinPrecompileSuffixSuccess bodyFullBuiltinECArithOperands
  bodyFullBuiltinECArithCompose bodyFullBuiltinECArithSuffix bodyFullBuiltinECArithStaging
  gasOutcomeFull gasOutcomeFullCompose gasShadowCompile
  exprSimHypsDefs exprLowering vyperAST list

val _ = Parse.hide "body";

Theorem ec_arith_builtin_vv_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (bt = ECAdd \/ bt = ECMul) /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  MATCH_MP_TAC ec_arith_vv_from_tail_full >>
  MATCH_MP_TAC ec_arith_tail_full_from_staging >>
  rpt gen_tac >> MATCH_ACCEPT_TAC ec_arith_staging_full_conditional
QED

Theorem ec_arith_builtin_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (bt = ECAdd \/ bt = ECMul) /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Builtin a bt args) es` by
    (MATCH_MP_TAC ec_arith_builtin_vv_sim_full >>
     qexistsl_tac [`tops`, `env`] >> asm_rewrite_tac []) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule expr_sim_full_of_vv >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> simp[]) >>
  qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _`
    (mp_tac o MATCH_MP exprSimHypsTheory.expr_body_pre_type_evaluates) >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  qexists_tac `x` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (Builtin a bt args)
     (es with gas_obs := gs)` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
  strip_tac >> gvs[] >> metis_tac[]
QED
