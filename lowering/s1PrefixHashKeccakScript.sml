(* Request-prefix companion to bodyFullHashKeccak. *)
Theory s1PrefixHashKeccak
Ancestors
  s1PrefixPreds bodyFullHashKeccak s1PrefixDefs
  exprSimHash exprSimHypsDefs exprSimSource exprLowering exprLoweringProps
  vyperTypeSystem compileEnv fragExec vyperState vyperInterpreter vyperContext
  gasShadowCompileStmtHelpers gasShadow gasShadowState

Theorem keccak_vv_sim_prefix:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx env ty ann e es.
  expr_body_pre cenv cx env (Builtin ann Keccak256 [e]) es /\
  expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (expr_type e) e es /\
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (expr_type e) e es ==>
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin ann Keccak256 [e]) es
Proof
  rpt gen_tac >> strip_tac >>
  `is_bytes_or_string_type (expr_type e) /\ ann = BaseT (BytesT (Fixed 32))` by
    (irule (SRULE [] (Q.INST [`b` |-> `Keccak256`,
       `ts` |-> `[expr_type e]`] hash_builtin_types)) >>
     gvs[expr_body_pre_def, well_typed_expr_def]) >>
  gvs[] >> simp[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr cenv ty (Builtin _ _ _) sa = _` mp_tac >>
  simp[compile_hash_singleton] >> pairarg_tac >> strip_tac >>
  gvs[] >>
  `cs_extends sa sm` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `?shadow_sm. lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) shadow_sa = (v,shadow_sm) /\ gas_shadow_state sm shadow_sm` by
    (qpat_x_assum `gas_shadow_state sb shadow_sb` kall_tac >>
     drule (REWRITE_RULE [gas_shadow_compiles_def]
       (Q.INST [`ty` |-> `expr_type e`, `sd` |-> `T`] gas_shadow_stmt_lower_value_env)) >>
     disch_then (qspecl_then [`e`, `cenv`] mp_tac) >> simp[] >> strip_tac >>
     Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sa` >> gvs[]) >>
  `?bty. expr_type e = BaseT bty` by
    (Cases_on `expr_type e` >> gvs[is_bytes_or_string_type_def]) >>
  `cs_extends sm sb` by
    (qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
     qmatch_goalsub_abbrev_tac `as_stack_val _ suffix` >>
     Cases_on `suffix` >> simp[as_stack_val_def] >> strip_tac >>
     gvs[markerTheory.Abbrev_def] >>
     Cases_on `bty` >> gvs[is_bytes_or_string_type_def,
       is_bytestring_type_def] >- metis_tac[hash_suffix_appends, cs_appends_def] >>
     rename1 `expr_type e = BaseT (BytesT bd)` >>
     Cases_on `bd` >> gvs[is_bytestring_type_def] >>
     metis_tac[hash_suffix_appends, cs_appends_def]) >>
  `cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sb` by
    (conj_tac >- (drule (cj 2 compile_expr_grows) >> simp[]) >>
     qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[gas_shadow_expr_def, gas_shadow_builtin_def, compile_hash_singleton] >>
     pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
     qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
     qmatch_goalsub_abbrev_tac `as_stack_val _ suffix` >>
     Cases_on `suffix` >> simp[as_stack_val_def] >> strip_tac >>
     gvs[markerTheory.Abbrev_def] >>
     Cases_on `bty` >> gvs[is_bytes_or_string_type_def,
       is_bytestring_type_def] >- metis_tac[hash_suffix_appends, cs_appends_def] >>
     rename1 `expr_type e = BaseT (BytesT bd)` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, as_stack_val_def] >>
     rpt strip_tac >> metis_tac[hash_suffix_appends, cs_appends_def]) >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fn_has_code_split] >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >>
     gvs[expr_body_pre_def]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`,
    `v`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[expr_sim_full_pre_def] >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  `eval_expr cx (Builtin (BaseT (BytesT (Fixed 32))) Keccak256 [e]) =
   bind (bind (eval_expr cx e) (read_result cx))
     (\v es. ((case builtin_result cx es.accounts (BaseT (BytesT (Fixed 32)))
       Keccak256 [expr_type e] [v] of INL w => INL (Value w) | INR exc => INR exc),es))` by
    (irule eval_expr_unary_builtin_action >>
     simp[vyperContextTheory.builtin_args_length_ok_def, is_self_codesize_def]) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `gas_prefix_full _ _ _ _ _`
    (qx_choose_then `marks` (CONJUNCTS_THEN2 assume_tac assume_tac) o
       ONCE_REWRITE_RULE[gas_prefix_full_def]) >>
  rewrite_tac[gas_prefix_full_def] >> qexists_tac `marks` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `monad_bind _ _ _ = _` mp_tac >>
  simp[Once bind_def] >>
  Cases_on `monad_bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail)` >>
  rename1 `monad_bind _ _ _ = (ans,mid)` >>
  Cases_on `ans` >> simp[] >> strip_tac >> gvs[] >> metis_tac[]
QED
