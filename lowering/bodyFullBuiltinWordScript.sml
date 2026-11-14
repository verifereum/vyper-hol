(*
 * The joint (full) judgments of the word-valued arithmetic builtins, at
 * every horizon (DF H, lo): source GAS origins, memory posts and pointer
 * ghosts share one witness.  bodyFullCases' word_builtin_expr_full_ok is
 * this, with body_expr_full_ok unfolded.
 *
 * The first premise is bodyFullExprGeneric's expr_vv_sim_stack_full
 * taken in its exact statement until it lands; it gives the
 * vv judgment of the stack-valued members from their value judgment.
 *
 * TOP-LEVEL:
 *   word_builtin_sim_full
 *)
Theory bodyFullBuiltinWord
Ancestors
  bodyFullPreds bodySimFull exprSimHypsDefs exprLowering vyperAST list
  bodyFullBuiltinWordNot bodyFullBuiltinWordNeg bodyFullBuiltinWordAbsCase
  bodyFullBuiltinWordWei bodyFullBuiltinWordRoundingCase
  bodyFullBuiltinWordModCompose bodyFullBuiltinWordModSuffix
  bodyFullBuiltinWordPowCompose bodyFullBuiltinWordPowSuffix

val _ = Parse.hide "body";

Theorem word_builtin_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (!DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty e es.
       (~is_word_type (expr_type e) ==>
        !tvt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) =
                SOME tvt ==>
              type_memory_size tvt = 0) /\
       expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cenv cx ty e es /\
       (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op,sb)) /\
       (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
       expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cenv cx ty e es) /\
    (bt = Not \/ bt = Neg \/ bt = Abs \/ (?dn. bt = AsWeiValue dn) \/ bt = Ceil \/
     bt = Floor \/ bt = AddMod \/ bt = MulMod \/ bt = PowMod256) /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >> strip_tac
  >- (irule word_not_sim_full >> metis_tac[])
  >- (irule word_neg_sim_full >> metis_tac[])
  >- (irule word_abs_sim_full >> metis_tac[])
  >- (irule word_wei_sim_full >> metis_tac[])
  >- (irule word_rounding_sim_full >> metis_tac[])
  >- (irule word_rounding_sim_full >> metis_tac[])
  >- (irule (MATCH_MP modular_sim_full_from_suffix modular_suffix_full) >>
      metis_tac[])
  >- (irule (MATCH_MP modular_sim_full_from_suffix modular_suffix_full) >>
      metis_tac[]) >>
  gvs[] >>
  irule (MATCH_MP pow_mod256_sim_full_from_suffix
    (Q.GENL [`DF`, `lo`, `explicit`, `ctx`, `func`, `PG`, `d`, `cenv`, `cx`,
             `st0`, `ee`, `sm`, `sb`, `x`, `y`, `op`, `t`, `G1`, `tn1`,
             `ann`, `ts`, `va`, `vb`] pow_mod256_suffix_full)) >>
  metis_tac[]
QED
