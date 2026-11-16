(* Empty length-word declaration: compiler witnesses joined with one joint runtime. *)
Theory bodyFullAnnAssignEmpty
Ancestors
  bodyFullAnnAssignEmptyEntry bodyFullAnnAssignEmptyRuntime
  gasShadowCompileStmtBase gasShadowState gasShadow
  bodyFullPreds bodySimFull bodySim exprSimHypsDefs supportedStmts
  supportedStmtTraverse bodyExprPreFacts vyperTypeInvariants
  compileEnv exprLowering stmtLowering loweringPosts vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map

Theorem body_annassign_memory_empty_full:
  !cx id typ e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_full_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~is_word_type typ /\
    0 < type_memory_bytes cenv typ /\
    (lowered_value_type cenv e = typ \/ is_bytestring_type typ \/
     has_length_word typ /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
    has_length_word typ /\ is_empty_value_expr e ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `body_stmt_safe tops (AnnAssign id typ e)` by
    metis_tac[supported_stmt_body_safe] >>
  `well_typed_expr env e /\ assignable_type env.type_defs typ /\
   type_widens_to env.type_defs (expr_type e) typ /\
   id NOTIN FDOM env.var_types` by gvs[type_stmt_def, AllCaseEqs()] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    metis_tac[assignable_type_well_formed, well_formed_type_def,
              optionTheory.IS_SOME_EXISTS] >>
  `body_expr_full_ok cx e` by
    (first_x_assum irule >> qexistsl [`es`,`es`,`get_tenv cx`,`tyv`] >>
     simp[lift_option_type_def, return_def]) >>
  `supported_expr tops e` by fs[supported_stmt_def] >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (Cases_on `FLOOKUP cenv.ce_vars id` >> simp[] >>
     fs[ce_locals_declared_def] >> metis_tac[]) >>
  rewrite_tac[stmt_frag_full_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all annassign_empty_full_code_entry >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  Cases_on `declare_local cenv id typ shadow_sa` >>
  rename1 `declare_local cenv id typ shadow_sa = (shadow_ce,shadow_r)` >>
  `shadow_ce = cenv' /\ gas_shadow_state r shadow_r` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `id` |-> `id`, `ty` |-> `typ`]
      gas_shadow_compiles_declare_local) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  qpat_x_assum `shadow_ce = cenv'` SUBST_ALL_TAC >>
  `compile_stmt cenv' lctx ret_ty (AnnAssign id typ (gas_shadow_expr e)) shadow_r =
    ((),shadow_sb)` by
    (qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     simp[stmt_env_def, declare_stmt_local_def, gas_shadow_stmt_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     Cases_on `compile_stmt cenv' lctx ret_ty
       (AnnAssign id typ (gas_shadow_expr e)) shadow_r` >> simp[]) >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `fn_has_code shadow_r shadow_sb shadow_func` by
    (`shadow_r = shadow_sa with cs_next_var := shadow_sa.cs_next_var + 1`
       by metis_tac[stmtSimPropsTheory.declare_local_ptr] >>
     simp[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
     metis_tac[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def]) >>
  drule_all annassign_empty_full_shadow_entry >> strip_tac >>
  irule annassign_empty_runtime_outcome >>
  qpat_assum `frame_ret_ok_full _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_sim_inv cenv cx env es` (irule_at Any) >>
  qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` (irule_at Any) >>
  simp[] >>
  qexistsl [`tops`,`shadow_r`,`shadow_b`,`shadow_a`,`bindings`] >>
  gns[] >> first_assum ACCEPT_TAC
QED
