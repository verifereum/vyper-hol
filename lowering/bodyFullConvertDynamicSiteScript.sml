(* The real and shadow Convert share the forced child and suffix split. *)
Theory bodyFullConvertDynamicSite
Ancestors
  s1PrefixDefs bodyFullShadowBodyInv exprSimConvert exprSimConvertFromBytes
  gasShadowCompile gasShadowState exprLoweringProps compileEnv exprSimSource
  typeBuiltinPrereqs exprSimHyps exprLowering vyperAST

Theorem convert_dynamic_child_site:
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  is_bytestring_type (expr_type e) /\ ~is_bytestring_type dst /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin ann Convert dst [e]) es
    (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0) ==>
  ann = dst /\ (?bt. dst = BaseT bt) /\ is_word_type dst /\
  well_formed_type env.type_defs dst /\ valid_conversion (expr_type e) dst /\
  expr_body_pre cenv cx env e es /\
  (?rty. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty /\
    (!gs tv ee v. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
      read_result cx tv ee = (INL v,ee) ==> value_has_type rty v)) /\
  (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
        ~is_word_type (post_value_type cenv e) ==>
        type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
        type_memory_size rt < 2**64) /\
  ?x sm shadow_sm.
    expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es (st0,sa,sm,shadow_sa,shadow_sm,x,s0,G0,tn0) /\
    cs_extends sa sm /\ cs_extends shadow_sa shadow_sm /\
    cs_extends sm sb /\ cs_extends shadow_sm shadow_sb /\
    fn_has_code sm sb func /\ fn_has_code shadow_sm shadow_sb shadow_func /\
    (if lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
        lowered_value_type cenv e = BaseT (StringT 0) then
       sm = sb /\ shadow_sm = shadow_sb /\ vv = StackValue dst (Lit 0w)
     else ?out. vv = StackValue dst out /\
       compile_type_convert x (mk_convert_op (expr_type e) dst) sm = (out,sb) /\
       compile_type_convert x (mk_convert_op (expr_type e) dst) shadow_sm = (out,shadow_sb))
Proof
  strip_tac >> drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  rename1 `valid_conversion (expr_type e) dst` >>
  `well_formed_type env.type_defs dst` by
    metis_tac[dynamic_convert_typing_boundary] >>
  `is_word_type dst /\ (!n. dst <> FlagT n)` by
    (drule_all dynamic_scalar_type >> simp[]) >>
  `?bt. dst = BaseT bt` by (Cases_on `dst` >> gvs[is_word_type_def]) >>
  gvs[] >>
  conj_tac
  >- (qpat_assum `expr_body_pre _ _ _ e _`
        (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
      simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
      rename1 `evaluate_type (get_tenv cx) (expr_type e) = SOME rty` >>
      qexists_tac `rty` >> simp[] >> rpt gen_tac >> strip_tac >>
      `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
      drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
      strip_tac >> gvs[] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> drule_all expr_body_pre_copy_ok >> simp[]) >>
  gvs[expr_vv_sim_full_pre_def] >>
  qpat_x_assum `compile_expr cenv ty (TypeBuiltin _ _ _ _) sa = _` mp_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def, exprCallBoundsTheory.expr_child_callback_def] >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (x,sm)` >>
  simp[exprBopLoweringTheory.lower_value_child_call, SF ETA_ss, expr_type_def] >>
  strip_tac >>
  `?shadow_sm. lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) shadow_sa = (x,shadow_sm) /\ gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
       (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
         (gas_shadow_expr e))` by
       irule gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env >>
     pop_assum (qspecl_then [`sa`,`shadow_sa`] mp_tac o
                REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sa` >> simp[]) >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    metis_tac[compile_expr_grows] >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gasShadowTheory.gas_shadow_expr_def] >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def, exprCallBoundsTheory.expr_child_callback_def] >>
  simp[exprBopLoweringTheory.lower_value_child_call, SF ETA_ss, expr_type_def] >>
  strip_tac >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    (Cases_on `lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
               lowered_value_type cenv e = BaseT (StringT 0)` >>
     gvs[exprBopLoweringTheory.as_stack_val_pair] >>
     metis_tac[cj 1 externalEntryShapeTheory.compile_type_convert_labels,
       pairTheory.SND, compileEnvTheory.cs_extends_refl]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[convert_operand_admissible,
      exprSimStackTheory.eval_expr_force_admissible, eval_expr_type_builtin_value] >>
  qexistsl_tac [`x`,`sm`,`shadow_sm`] >>
  simp[expr_sim_full_pre_def] >>
  conj_tac >- metis_tac[fragExecTheory.fn_has_code_split] >>
  conj_tac >- metis_tac[fragExecTheory.fn_has_code_split] >>
  conj_tac >- metis_tac[fragExecTheory.fn_has_code_split] >>
  Cases_on `lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
            lowered_value_type cenv e = BaseT (StringT 0)` >>
  gvs[exprBopLoweringTheory.as_stack_val_pair] >> metis_tac[pairTheory.PAIR]
QED
