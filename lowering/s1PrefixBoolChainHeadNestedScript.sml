(* Prefix companion for the nested BoolChain dispatcher entry. *)
Theory s1PrefixBoolChainHeadNested
Ancestors
  s1PrefixBoolChainNestedReadEvidence s1PrefixBoolChainUniformEntries
  s1PrefixBoolChainNestedDemandStep s1PrefixCheckedContextFull s1PrefixBoolChainEqDemand gasShadowBoolChainOperands boolChainWrapperRead
  s1PrefixOfVV s1PrefixPreds s1PrefixDefs
  bodyFullBoolChain bodyFullPreds bodySimFull exprLoweringProps
  exprBodyPreProps exprSimHyps boolChainCodeLayout compileEnv vyperContext vyperTypeSystem exprLowering vyperInterpreter vyperAST list

Theorem bool_chain_head_nested_prefix_ok:
  !cx ann p n args.
    (!a. expr_size a < expr_size (Builtin ann (BoolChain p n) args) ==>
      body_expr_prefix_ok cx a) ==>
    body_expr_prefix_ok cx (Builtin ann (BoolChain p n) args)
Proof
  rpt gen_tac >> disch_tac >> simp[Once body_expr_prefix_ok_def] >>
  rpt gen_tac >> strip_tac >>
  drule_then strip_assume_tac checked_context_full_exprs >>
  drule expr_body_pre_static_facts >> strip_tac >>
  gvs[well_typed_expr_def, well_typed_builtin_app_def] >>
  conj_asm1_tac
  >- (pure_rewrite_tac[expr_sim_prefix_def, expr_sim_full_pre_def] >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `lower_value compile_expr _ _ _ _ = _` mp_tac >>
      simp[lower_value_def, comp_bind_def] >> pairarg_tac >> strip_tac >>
      qpat_x_assum `lower_value compile_expr _ _ _ _ = _` mp_tac >>
      simp[lower_value_def, comp_bind_def] >> pairarg_tac >> strip_tac >>
      qpat_assum `compile_expr _ _ (Builtin _ (BoolChain _ _) [_]) _ = _`
        (mp_then Any strip_assume_tac bool_chain_root_layout) >>
      qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
        (strip_assume_tac o MATCH_MP bool_chain_root_layout o
         SIMP_RULE (srw_ss()) [gasShadowTheory.gas_shadow_expr_def,
                              gasShadowTheory.gas_shadow_builtin_def]) >>
      gvs[gas_shadow_bool_chain_operands, unwrap_value_def, comp_return_def] >>
      `gas_admissible (eval_expr cx (Builtin (BaseT BoolT) (BoolChain p n) [x0]))
         expr_vv_res_ok es` by
        (irule expr_body_pre_vv_gas_admissible >>
         qexistsl_tac [`cenv`,`env`] >> first_assum ACCEPT_TAC) >>
      `expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
         cenv cx ty (Builtin (BaseT BoolT) (BoolChain p n) [x0]) es
         (st0,sa,cs'',shadow_sa,cs',StackValue (BaseT BoolT) (Var rv),s0,G0,tn0)` by
        (pure_rewrite_tac[expr_vv_sim_full_pre_def] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC)) >>
      irule bool_chain_nested_read_prefix_from_joint_smaller >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      simp[builtin_args_length_ok_def] >>
      qexistsl_tac [`cenv`,`d`,`env`,`rv`,`sa`,`cs''`,`shadow_func`,
        `shadow_sa`,`cs'`,`tops`,`ty`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `value_read_demand _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE[value_read_demand_def, expr_sim_full_pre_def]) >>
      `body_expr_prefix_ok cx a` by
        (first_x_assum irule >> simp[]) >>
      qpat_x_assum `body_expr_prefix_ok cx a`
        (mp_tac o REWRITE_RULE[body_expr_prefix_ok_def]) >>
      disch_then strip_assume_tac >>
      qpat_assum `!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es. _`
        (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,
          `func`,`shadow_func`,`cenv`,`env`,`ety`,`ee`] mp_tac) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      strip_tac >>
      qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE[expr_sim_prefix_def, expr_sim_full_pre_def]) >>
      disch_then (qspecl_then [`st0`,`ca`,`cb`,`sha`,`shb`,`op'`,`u`,`J`,`tau`] mp_tac) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      strip_tac)
  >> (irule expr_vv_sim_stack_prefix >>
      conj_tac
      >- (gen_tac >> Cases_on `compile_expr cenv ty
             (Builtin (BaseT BoolT) (BoolChain p n) [x0]) sa` >>
          drule bool_chain_root_layout >> strip_tac >> simp[])
      >- (rpt gen_tac >> strip_tac >> metis_tac[eval_expr_builtin_value]))
QED
