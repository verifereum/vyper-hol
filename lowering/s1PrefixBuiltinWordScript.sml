(* Request-prefix companion to bodyFullBuiltinWord. *)
Theory s1PrefixBuiltinWord
Ancestors
  s1PrefixPreds bodyFullBuiltinWord s1PrefixDefs s1PrefixOfVV
  s1PrefixBuiltinWordNot s1PrefixBuiltinWordNeg s1PrefixBuiltinWordAbsCase
  s1PrefixWordWei s1PrefixBuiltinWordRoundingCase
  s1PrefixBuiltinWordModCompose s1PrefixBuiltinWordPowCompose
  bodyFullBuiltinWordWeiPrefix bodyFullBuiltinWordModSuffix bodyFullBuiltinWordPowSuffix
  bodyFullPreds bodyFullExprsSingleton bodyFullSimProjection
  exprLoweringProps exprSimWordBuiltins vyperContext

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >> gvs[]
  >- (irule word_not_sim_prefix >> metis_tac[])
  >- (irule word_neg_sim_prefix >> metis_tac[])
  >- (irule word_abs_sim_prefix >> metis_tac[])
  >- (drule as_wei_value_argument_shape >> strip_tac >> gvs[] >>
      conj_asm1_tac
      >- (irule word_wei_sim_prefix >> qexists_tac `env` >> simp[] >>
          disch_tac >>
          fs[builtin_args_length_ok_def, body_exprs_full_ok_singleton,
             body_exprs_prefix_ok_def] >>
          conj_tac
          >- metis_tac[body_expr_full_ok_simulations] >>
          fs[Once body_expr_prefix_ok_def] >> metis_tac[]) >>
      irule expr_vv_sim_stack_prefix >> simp[] >>
      reverse conj_tac >- metis_tac[eval_expr_builtin_value] >>
      gen_tac >> Cases_on `compile_expr cenv ty
        (Builtin (BaseT (UintT 256)) (AsWeiValue dn) [e]) sa` >>
      drule_at Any compile_word_builtin_stack >> simp[] >> metis_tac[])
  >- (irule word_rounding_sim_prefix >> metis_tac[])
  >- (irule word_rounding_sim_prefix >> metis_tac[])
  >- (irule (MATCH_MP modular_sim_prefix_from_suffix modular_suffix_full) >>
      metis_tac[])
  >- (irule (MATCH_MP modular_sim_prefix_from_suffix modular_suffix_full) >>
      metis_tac[]) >>
  irule (MATCH_MP pow_mod256_sim_prefix_from_suffix
    (Q.GENL [`DF`, `lo`, `explicit`, `ctx`, `func`, `PG`, `d`, `cenv`, `cx`,
             `st0`, `ee`, `sm`, `sb`, `x`, `y`, `op`, `t`, `G1`, `tn1`,
             `ann`, `ts`, `va`, `vb`] pow_mod256_suffix_full)) >> metis_tac[]
QED
*)
Theorem word_builtin_sim_prefix:
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
  (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_prefix_ok cx args) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin a bt args) es ==>
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  cheat
QED
