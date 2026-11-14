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
  rpt gen_tac >> strip_tac >>
  `a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
   ?e1 e2. args = [e1;e2] /\
     expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
     expr_type e2 = (if bt = ECAdd then
       ArrayT (BaseT (UintT 256)) (Fixed 2) else BaseT (UintT 256))` by
    (Cases_on `bt = ECAdd` >> gvs[] >> metis_tac[ec_pre_types]) >>
  `body_exprs_full_ok cx [e1;e2]` by
    (gvs[vyperContextTheory.builtin_args_length_ok_def]) >>
  simp[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  FAIL_TAC "EC assembly boundary"
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
  rpt strip_tac
QED
