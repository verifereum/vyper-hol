(* Request-prefix companion to bodyFullAbiDecodeExprConditional. *)
Theory s1PrefixAbiDecodeExprConditional
Ancestors
  s1PrefixPreds bodyFullAbiDecodeExprConditional s1PrefixDefs s1PrefixOfVV
  exprSimSliceCompose exprSimAbiDecodeBodySuccess vyperState
  gasShadow gasShadowState gasShadowCompileStmtHelpers
  exprBodyPreProps exprSimAbiDecodeEntryTyping exprOpenFirstOperand

Theorem abi_decode_singleton_vv_prefix:
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty0 (TypeBuiltin ty (AbiDecode unwrap) ty [e]) es
Proof
  strip_tac >>
  simp[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all abi_decode_singleton_compile >> strip_tac >>
  `?shadow_start. lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
     (gas_shadow_expr e) shadow_sa = (data,shadow_start) /\
     gas_shadow_state start shadow_start` by
    (qpat_assum `gas_shadow_state sa shadow_sa`
       (mp_then Any mp_tac (REWRITE_RULE [gas_shadow_compiles_def]
         (Q.INST [`sd` |-> `T`] gas_shadow_stmt_lower_value_env))) >>
     disch_then (qspecl_then [`expr_type e`,`e`,`ce`] mp_tac) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
       (gas_shadow_expr e) shadow_sa` >> simp[]) >>
  `fn_has_code shadow_sa shadow_start shadow_func` by
    (qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gas_shadow_expr_def, NoAsms] >> strip_tac >>
     `expr_type (gas_shadow_expr e) = BaseT (BytesT (Dynamic n))` by simp[] >>
     drule_all abi_decode_singleton_compile >> simp[] >> strip_tac >> gvs[]) >>
  qpat_assum `gas_admissible (eval_expr cx _) expr_vv_res_ok es`
    (mp_tac o REWRITE_RULE [abi_decode_singleton_source]) >>
  disch_then (assume_tac o MATCH_MP slice_gas_admissible_expr_head) >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ e _`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def, expr_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`start`,`shadow_sa`,`shadow_start`,
    `data`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  `!qe. SND (eval_expr cx (TypeBuiltin ty (AbiDecode unwrap) ty [e]) qe) =
        SND (bind (eval_expr cx e) (read_result cx) qe)` by
    (POP_ASSUM_LIST (K ALL_TAC) >>
     rewrite_tac[abi_decode_singleton_source, bind_def] >> gen_tac >>
     Cases_on `eval_expr cx e qe` >> rename1 `_ = (res,ee)` >>
     Cases_on `res` >> simp[] >>
     rename1 `read_result cx raw ee` >>
     Cases_on `read_result cx raw ee` >> rename1 `_ = (res',ee')` >>
     Cases_on `res'` >> simp[lift_sum_def, return_def, raise_def] >>
     rename1 `evaluate_type_builtin cx (AbiDecode unwrap) ty _ [v]` >>
     Cases_on `evaluate_type_builtin cx (AbiDecode unwrap) ty [expr_type e] [v]` >>
     simp[bind_def, return_def, raise_def]) >>
  drule gas_prefix_full_state_cong >> simp[]
QED

Theorem abi_decode_expr_prefix:
  !cx v11 b typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok (AbiDecode b) (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_full_ok cx es) /\
    (!s'' x t.
       type_check (type_builtin_args_length_ok (AbiDecode b) (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_prefix_ok cx es) ==>
    body_expr_prefix_ok cx (TypeBuiltin v11 (AbiDecode b) typ es)
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once body_expr_prefix_ok_def] >> rpt gen_tac >> strip_tac >>
  drule expr_body_pre_static_facts >> strip_tac >>
  drule abi_decode_parent_type >> strip_tac >> gvs[] >>
  `body_exprs_prefix_ok cx [e]` by
    (first_x_assum irule >>
     simp[vyperStateTheory.type_check_def,
          vyperContextTheory.type_builtin_args_length_ok_def,
          vyperStateTheory.assert_def, vyperStateTheory.return_def]) >>
  drule expr_body_pre_type_builtin_head >> strip_tac >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
       cenv cx (expr_type e) e es'` by
    (qpat_assum `body_exprs_prefix_ok _ [_]`
       (mp_tac o SIMP_RULE (srw_ss()) [body_exprs_prefix_ok_def]) >>
     disch_then (drule_all o cj 1 o CONJUNCT1 o
       ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >> simp[]) >>
  reverse conj_asm2_tac
  >- (irule abi_decode_singleton_vv_prefix >> simp[] >> metis_tac[]) >>
  irule expr_sim_prefix_of_vv >> simp[]
QED
