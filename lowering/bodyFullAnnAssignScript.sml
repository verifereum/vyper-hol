(*
 * Annotated declaration over the finite-horizon joint judgment.
 * Stated over the finite-horizon full family (bodySimFull), one sub-shape
 * per S1 dispatch arm of bodySimStmtCases/bodySimDeclCases, so the case in
 * bodyFullCases closes by the same case split.
 *
 * TOP-LEVEL: the body_*_full sub-shape theorems below.
 *)
Theory bodyFullAnnAssign
Ancestors
  bodyFullAnnAssignWordEntry bodyFullAnnAssignReserve bodyFullAnnAssignCompose
  bodyFullPathHistory bodyInvNoDalloca annAssignPtrFacts bodyExprPreFacts
  stmtSimDeclSource exprSimSource exprLoweringProps supportedStmtTraverse loweringPosts
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  compileEnv exprLowering stmtLowering vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map

val _ = Parse.hide "body";

(* A word local. *)
Theorem body_annassign_word_full:
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
    is_word_type typ ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  rpt gen_tac >> strip_tac >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  `assignable_type env.type_defs typ` by
    gvs[type_stmt_def, AllCaseEqs()] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    metis_tac[assignable_type_well_formed, well_formed_type_def,
              optionTheory.IS_SOME_EXISTS] >>
  `body_expr_full_ok cx e` by
    (first_x_assum irule >>
     qexistsl_tac [`es`, `es`, `get_tenv cx`, `tyv`] >>
     simp[lift_option_type_def, return_def]) >>
  `expr_type e = typ` by
    (irule type_widens_to_word >> simp[] >>
     qexists_tac `env.type_defs` >>
     gvs[type_stmt_def, AllCaseEqs()]) >>
  `well_typed_expr env e /\ id NOTIN FDOM env.var_types` by
    gvs[type_stmt_def, AllCaseEqs()] >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule bodySimDeclCasesTheory.declared_name_unbound >> metis_tac[]) >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `body_stmt_safe tops (AnnAssign id typ e)` by
    metis_tac[supported_stmt_body_safe] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `declare_local cenv id typ sa` >> rename1 `declare_local _ _ _ _ = (ce,r)` >>
  `ce = cenv' /\ compile_stmt ce lctx ret_ty (AnnAssign id typ e) r = ((),sb)` by
    (qpat_x_assum `stmt_env cenv _ _ _ sa = _` mp_tac >>
     simp[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_return_def,
          comp_ignore_bind_def] >>
     Cases_on `compile_stmt ce lctx ret_ty (AnnAssign id typ e) r` >>
     simp[] >> Cases_on `q` >> simp[]) >>
  gvs[] >>
  drule_all annassign_declared_rhs_pre_ptr >> strip_tac >>
  drule_all annassign_word_full_declared_layout >> strip_tac >>
  Cases_on `declare_local cenv id (expr_type e) shadow_sa` >>
  rename1 `declare_local _ _ _ shadow_sa = (shadow_ce,shadow_r)` >>
  `shadow_ce = ce /\ gas_shadow_state r shadow_r` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `id` |-> `id`, `ty` |-> `expr_type e`]
       gasShadowCompileStmtBaseTheory.gas_shadow_compiles_declare_local) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  gvs[] >>
  `compile_stmt ce lctx ret_ty (AnnAssign id (expr_type e) (gas_shadow_expr e))
     shadow_r = ((),shadow_sb)` by
    (qpat_x_assum `stmt_env cenv _ _ _ shadow_sa = _` mp_tac >>
     simp[stmt_env_def, declare_stmt_local_def, gas_shadow_stmt_def,
          comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
     Cases_on `compile_stmt ce lctx ret_ty
       (AnnAssign id (expr_type e) (gas_shadow_expr e)) shadow_r` >>
     simp[] >> Cases_on `q` >> simp[]) >>
  `fn_has_code shadow_r shadow_sb shadow_func` by
    (drule_all stmtSimPropsTheory.declare_local_ptr >> strip_tac >>
     fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def]) >>
  drule_all (SRULE [] (Q.INST [`typ` |-> `expr_type e`, `sz` |-> `32`]
    annassign_word_full_shadow_parts)) >> strip_tac >>
  cheat
QED

(* A memory local whose source is stored at its own layout. *)
Theorem body_annassign_memory_full:
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
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  cheat
QED

(* A memory local whose source is a widened aggregate. *)
Theorem body_annassign_widened_full:
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
    ~(lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  cheat
QED

(* Any other declared type. *)
Theorem body_annassign_other_full:
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
    ~(expr_type e = typ \/ is_bytestring_type typ \/
      has_length_word typ /\ is_empty_value_expr e) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  cheat
QED
