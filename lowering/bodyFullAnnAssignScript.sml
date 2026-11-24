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
  bodyFullShadowBodyInv
  bodyFullAnnAssignWord bodyFullAnnAssignWidened bodyFullAnnAssignMemoryPost
  bodyFullAnnAssignMemory bodyFullAnnAssignOther bodyFullShared exprSimAggregateLayout typedMemoryCopy
  bodyDeclCopyMemory vyperTypeInvariants allocLimits
  bodyFullIfExpReach bodyFullHashKeccakFixed loweringPosts
  vyperTypeCallGraph supportedExprTraverse
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  bodySimDeclCases bodyExprPreFacts exprSimHyps exprSimSource
  supportedStmtTraverse vyperTypeArgFits
  compileEnv exprLowering stmtLowering vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map

val _ = Parse.hide "body";

Theorem type_stmt_annassign[local]:
  type_stmt env ret_ty (AnnAssign id typ e) =
    (if well_typed_expr env e /\ assignable_type env.type_defs typ /\
        type_widens_to env.type_defs (expr_type e) typ /\
        id NOTIN FDOM env.var_types
     then SOME (extend_local env id typ T) else NONE)
Proof
  simp[Once type_stmt_def]
QED

Theorem supported_stmt_annassign[local]:
  supported_stmt tops bindings (AnnAssign id typ e) =
    (supported_place_type tops typ /\ supported_expr tops e)
Proof
  simp[Once supported_stmt_def]
QED

Theorem annassign_full_declared_rhs_pre[local]:
  body_stmt_safe tops (AnnAssign id typ e) /\
  body_inv tops ctx cenv cx /\ supported_expr tops e /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (AnnAssign id typ e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
  id NOTIN FDOM env.var_types /\ FLOOKUP cenv.ce_vars id = NONE /\
  stmt_exprs_ok cenv (AnnAssign id typ e) /\
  call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
  declare_local cenv id typ st = (c,st1) ==>
  body_inv tops ctx c cx /\ expr_body_pre c cx env e es
Proof
  strip_tac >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `same_frame cenv c` by
    (drule_then irule declare_local_same_frame >> simp[]) >>
  `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
  `stmt_exprs_ok c (AnnAssign id typ e)` by
    metis_tac[annassign_declare_exprs_ok] >>
  `expr_sim_inv c cx env es` by metis_tac[expr_sim_inv_declare_local] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule body_annassign_rhs_pre >> metis_tac[]
QED

Theorem annassign_word_full_source[local]:
  (!tenv s'' tyv t.
    tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
      (INL tyv,t) ==> body_expr_full_ok cx e) /\
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AnnAssign id typ e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (AnnAssign id typ e) ==> occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
  stmt_exprs_ok cenv (AnnAssign id typ e) /\
  call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
  is_word_type typ ==>
  well_typed_expr env e /\ expr_type e = typ /\
  id NOTIN FDOM env.var_types /\ cenv.ce_alloca_locals /\
  supported_expr tops e /\ expr_body_pre cenv cx env e es /\
  body_expr_full_ok cx e /\
  ?tyv. evaluate_type (get_tenv cx) typ = SOME tyv
Proof
  strip_tac >>
  `well_typed_expr env e /\ expr_type e = typ /\
   id NOTIN FDOM env.var_types` by
    (gvs[type_stmt_annassign, AllCaseEqs()] >>
     metis_tac[type_widens_to_word]) >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `supported_expr tops e` by fs[supported_stmt_annassign] >>
  `body_stmt_safe tops (AnnAssign id typ e)` by
    metis_tac[supported_stmt_body_safe] >>
  `expr_body_pre cenv cx env e es` by
    metis_tac[body_annassign_rhs_pre] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    (drule expr_body_pre_type_evaluates >>
     simp[optionTheory.IS_SOME_EXISTS]) >>
  `body_expr_full_ok cx e` by
    (first_x_assum irule >>
     qexistsl_tac [`es`, `es`, `get_tenv cx`, `tyv`] >>
     simp[lift_option_type_def, return_def]) >>
  simp[] >> metis_tac[]
QED

(* Use the RHS simulation clause with the real declaration's typing facts. *)
fun annassign_rhs_sim_tac g =
  (qpat_assum `body_expr_full_ok _ _`
     (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
   qpat_assum `!DF lo d PG tops ctx sc f sf ce env ty es.
                 _ ==> expr_sim_full _ _ _ _ _ _ /\ expr_vv_sim_full _ _ _ _ _ _`
     (drule_all_then strip_assume_tac) >>
   simp[]) g;

(* A word local. *)
Theorem body_annassign_word_full:
  !cx id typ e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_full_ok cx e) /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
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
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  rpt gen_tac >> strip_tac >>
  drule_all annassign_word_full_source >> strip_tac >>
  drule_all_then strip_assume_tac bodySingletonCallSupportTheory.supported_singleton_expr_body_calls >>
  rw[stmt_frag_full_def] >>
  fs[stmt_env_def, declare_stmt_local_def, gas_shadow_stmt_def,
     comp_bind_def, comp_ignore_bind_def, comp_return_def,
     pairTheory.pair_case_thm] >>
  Cases_on `declare_local cenv id (expr_type e) sa` >>
  rename1 `declare_local _ _ _ sa = (decl_ce,r)` >>
  Cases_on `declare_local (gas_shadow_env T cenv) id (expr_type e) shadow_sa` >>
  rename1 `declare_local _ _ _ shadow_sa = (shadow_decl_ce,r')` >>
  `shadow_decl_ce = gas_shadow_env T decl_ce /\ gas_shadow_state r r'` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `id` |-> `id`,
       `ty` |-> `expr_type e`, `sd` |-> `T`]
       (REWRITE_RULE [gasShadowCompileStmtBaseTheory.gas_shadow_compiles_env_def]
         gasShadowCompileStmtBaseTheory.gas_shadow_compiles_env_declare_local)) >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  qpat_x_assum `shadow_decl_ce = _` SUBST_ALL_TAC >>
  Cases_on `compile_stmt decl_ce lctx ret_ty (AnnAssign id (expr_type e) e) r` >>
  Cases_on `compile_stmt (gas_shadow_env T decl_ce) lctx ret_ty
              (AnnAssign id (expr_type e) (gas_shadow_expr e)) r'` >>
  gvs[] >>
  rename1 `declare_local _ _ _ sa = (rhs_ce,r)` >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (Cases_on `FLOOKUP cenv.ce_vars id` >> simp[] >>
     fs[ce_locals_declared_def] >> metis_tac[]) >>
  `body_stmt_safe tops (AnnAssign id (expr_type e) e)` by
    metis_tac[supported_stmt_body_safe] >>
  drule_all_then strip_assume_tac annassign_full_declared_rhs_pre >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      rhs_ce cx (expr_type e) e es` by
    annassign_rhs_sim_tac >>
  `lookup_scopes id es.scopes = NONE` by
    (fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
         vyperTypeInvariantsTheory.env_scopes_consistent_def] >>
     Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     qpat_x_assum `!id entry. lookup_scopes _ _ = _ ==> _`
       (drule_then mp_tac) >> simp[FLOOKUP_DEF]) >>
  `ctx_has_dalloca ctx ==>
    (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s)` by
    metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
  drule_all annassign_word_full_execution_sep >>
  disch_then (qspec_then `RetQ` assume_tac) >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (fn outcome =>
    qpat_assum `return_buf_frame d cenv sa s0` (fn frame =>
      qpat_assum `return_buf_sep d cenv es s0` (fn sep =>
        mp_tac (MATCH_MP gas_outcome_full_return_buf_allocas
          (LIST_CONJ [outcome,frame,sep]))))) >>
  disch_then (fn th => irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
    irule_at Any th) >>
  simp[] >> rpt strip_tac >> qexists_tac `ce` >> simp[] >>
  conj_tac
  >- first_assum (ACCEPT_TAC o MATCH_MP
       bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  first_assum ACCEPT_TAC
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
    shadow_body_inv tops ctx shadow_ctx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
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
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `well_typed_expr env e /\ assignable_type env.type_defs typ /\
   type_widens_to env.type_defs (expr_type e) typ /\
   id NOTIN FDOM env.var_types` by
    gvs[type_stmt_annassign, AllCaseEqs()] >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    metis_tac[assignable_type_well_formed, well_formed_type_def,
              optionTheory.IS_SOME_EXISTS] >>
  `body_expr_full_ok cx e` by
    (first_x_assum irule >>
     qexistsl_tac [`es`,`es`,`get_tenv cx`,`tyv`] >>
     simp[lift_option_type_def, return_def]) >>
  `supported_expr tops e` by fs[supported_stmt_annassign] >>
  `body_stmt_safe tops (AnnAssign id typ e)` by
    metis_tac[supported_stmt_body_safe] >>
  `expr_body_pre cenv cx env e es` by metis_tac[body_annassign_rhs_pre] >>
  `lookup_scopes id es.scopes = NONE` by
    (fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     qpat_x_assum `!id entry. lookup_scopes _ _ = _ ==> _`
       (drule_then mp_tac) >> simp[FLOOKUP_DEF]) >>
  `lowered_value_type cenv e = expr_type e \/
   is_bytestring_type (expr_type e) \/
   is_bytestring_type (lowered_value_type cenv e) \/
   arg_type_fits (lowered_value_type cenv e) (expr_type e)` by
    (qpat_assum
       `lowered_value_type cenv e = expr_type e \/ _ /\ _ /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  irule annassign_memory_full_execution >>
  rpt (conj_tac ORELSE qexistsl_tac [`env`,`tops`]) >>
  simp[] >>
  rpt gen_tac >> disch_tac >>
  drule_all_then strip_assume_tac annassign_full_declared_rhs_pre >>
  annassign_rhs_sim_tac
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
    shadow_body_inv tops ctx shadow_ctx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
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
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  rpt gen_tac >> strip_tac >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `well_typed_expr env e /\ assignable_type env.type_defs typ /\
   type_widens_to env.type_defs (expr_type e) typ /\
   id NOTIN FDOM env.var_types` by
    gvs[type_stmt_annassign, AllCaseEqs()] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    metis_tac[assignable_type_well_formed, well_formed_type_def,
              optionTheory.IS_SOME_EXISTS] >>
  `body_expr_full_ok cx e` by
    (first_x_assum irule >>
     qexistsl_tac [`es`, `es`, `get_tenv cx`, `tyv`] >>
     simp[lift_option_type_def, return_def]) >>
  `supported_expr tops e` by fs[supported_stmt_annassign] >>
  `body_stmt_safe tops (AnnAssign id typ e)` by
    metis_tac[supported_stmt_body_safe] >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `lookup_scopes id es.scopes = NONE` by
    (fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     qpat_x_assum `!id entry. lookup_scopes _ _ = _ ==> _`
       (drule_then mp_tac) >> simp[FLOOKUP_DEF]) >>
  `type_memory_bytes cenv typ < 2 ** 64` by
    fs[stmt_exprs_ok_def, alloc_limits_stmt_def, type_alloc_ok_def] >>
  irule annassign_widened_full_execution >>
  simp[] >> qexistsl_tac [`env`, `tops`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_all annassign_full_declared_rhs_pre >> strip_tac >>
  drule_all declare_local_memory_types_mem >> strip_tac >>
  annassign_rhs_sim_tac >>
  qpat_assum `~(lowered_value_type cenv e = _ \/ _)` mp_tac >> simp[]
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
    shadow_body_inv tops ctx shadow_ctx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
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
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  rpt gen_tac >> strip_tac >>
  `well_typed_expr env e /\ assignable_type env.type_defs typ /\
   type_widens_to env.type_defs (expr_type e) typ /\
   id NOTIN FDOM env.var_types` by
    gvs[type_stmt_annassign, AllCaseEqs()] >>
  `~is_bytestring_type (expr_type e)` by
    metis_tac[type_widens_from_bytestring] >>
  Cases_on `lowered_value_type cenv e = expr_type e`
  >- (`FLOOKUP cenv.ce_vars id = NONE` by
        (irule declared_name_unbound >> metis_tac[]) >>
      `env.type_defs = get_tenv cx` by
        gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
      `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
        metis_tac[assignable_type_well_formed, well_formed_type_def,
                  optionTheory.IS_SOME_EXISTS] >>
      `body_expr_full_ok cx e` by
        (first_x_assum irule >>
         qexistsl_tac [`es`, `es`, `get_tenv cx`, `tyv`] >>
         simp[lift_option_type_def, return_def]) >>
      `supported_expr tops e` by fs[supported_stmt_annassign] >>
      `body_stmt_safe tops (AnnAssign id typ e)` by
        metis_tac[supported_stmt_body_safe] >>
      `expr_body_pre cenv cx env e es` by metis_tac[body_annassign_rhs_pre] >>
      `?stv. evaluate_type (get_tenv cx) (expr_type e) = SOME stv` by
        metis_tac[expr_body_pre_type_evaluates, optionTheory.IS_SOME_EXISTS] >>
      `lookup_scopes id es.scopes = NONE` by
        (fs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
         Cases_on `lookup_scopes id es.scopes` >> simp[] >>
         qpat_x_assum `!id entry. lookup_scopes _ _ = _ ==> _`
           (drule_then mp_tac) >> simp[FLOOKUP_DEF]) >>
      irule annassign_other_typed_full_execution >>
      fs[] >> qexistsl_tac [`env`, `tops`] >> simp[] >>
      rpt gen_tac >> strip_tac >>
      drule_all_then strip_assume_tac annassign_full_declared_rhs_pre >>
      annassign_rhs_sim_tac) >>
  irule body_annassign_widened_full >> simp[] >>
  metis_tac[annassign_memory_bytes_pos_ptr]
QED
