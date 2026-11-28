(* Prefix companion for the nested BoolChain dispatcher entry. *)
Theory s1PrefixBoolChainHeadNested
Ancestors
  s1PrefixBoolChainActualHistory s1PrefixBoolChainHeadAlternative
  s1PrefixBoolChainNestedEntry s1PrefixBoolChainUniformEntries
  s1PrefixBoolChainNestedDemandStep s1PrefixCheckedContextFull s1PrefixBoolChainEqDemand gasShadowBoolChainOperands boolChainWrapperRead
  s1PrefixOfVV s1PrefixPreds s1PrefixDefs
  vyperTypeCallGraph alist
  bodyFullBoolChain bodyFullPreds bodySimFull exprLoweringProps
  exprBodyPreProps exprSimHyps boolChainCodeLayout compileEnv vyperContext vyperTypeSystem exprLowering vyperInterpreter vyperAST list

Theorem bool_chain_full_from_members[local]:
  !xs. EVERY (body_expr_full_ok cx) xs ==> bool_chain_full_ok [(NONE,cx_tops cx)] [] cx xs
Proof
  Induct_on `xs` >> simp[bool_chain_full_ok_def]
QED

Theorem bool_chain_head_nested_prefix_ok:
  !cx ann p n args.
    (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
      EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
        (vyperTypeCallGraph$int_calls_expr (Builtin ann (BoolChain p n) args))) /\
    (!a. expr_size a < expr_size (Builtin ann (BoolChain p n) args) /\
      (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
        EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
          (vyperTypeCallGraph$int_calls_expr a)) ==>
      body_expr_prefix_ok cx a) ==>
    body_expr_prefix_ok cx (Builtin ann (BoolChain p n) args)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_expr_prefix_ok_def] >>
  rpt gen_tac >> strip_tac >>
  drule_then strip_assume_tac checked_context_full_exprs >>
  drule expr_body_pre_static_facts >> strip_tac >>
  gvs[well_typed_expr_def, well_typed_builtin_app_def] >>
  `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by
    fs[body_const_cells_agree_def] >>
  `EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
      (int_calls_expr x0)` by
    (res_tac >> fs[int_calls_expr_def, EVERY_APPEND]) >>
  `bool_chain_full_ok [(NONE,cx_tops cx)] [] cx (bool_chain_operands p (n - 1) x0)` by
    (irule bool_chain_full_from_members >>
     qpat_assum `EVERY _ (int_calls_expr x0)`
       (fn th => assume_tac (MATCH_MP (Q.SPECL [`n - 1`, `p`, `x0`]
         bool_chain_operands_calls) th)) >>
     fs[EVERY_MEM] >> metis_tac[]) >>
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
      irule bool_chain_nested_prefix_at_entry >>
      qhdtm_assum `expr_vv_sim_full_pre` (irule_at Any) >>
      qhdtm_assum `body_const_cells_agree` (irule_at Any) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      TRY (simp[builtin_args_length_ok_def] >> NO_TAC) >>
      rpt strip_tac >>
      drule_all bool_chain_actual_reached_calls >> simp[] >> strip_tac >>
      `body_expr_prefix_ok cx a` by
        (qpat_assum `!a. expr_size a < _ /\ _ ==> _` irule >>
         fs[expr_size_def] >> decide_tac) >>
      qpat_x_assum `body_expr_prefix_ok cx a`
        (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
      disch_then drule_all >> simp[expr_sim_prefix_def] >> metis_tac[])
  >> (irule expr_vv_sim_stack_prefix >>
      conj_tac
      >- (gen_tac >> Cases_on `compile_expr cenv ty
             (Builtin (BaseT BoolT) (BoolChain p n) [x0]) sa` >>
          drule bool_chain_root_layout >> strip_tac >> simp[])
      >- (rpt gen_tac >> strip_tac >> metis_tac[eval_expr_builtin_value]))
QED
