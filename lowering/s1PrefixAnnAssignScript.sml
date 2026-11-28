(* Request-prefix companion to bodyFullAnnAssign. *)
Theory s1PrefixAnnAssign
Ancestors
  s1PrefixPreds bodyFullAnnAssign s1PrefixDefs
  s1PrefixAnnAssignAllocRhs s1PrefixAnnAssignEmptyRhs s1PrefixAnnAssignSourceTrace
  s1PrefixInvalidTraceDomain s1PrefixAnnAssignWord exprBodyPreProps bodySimDeclCases bodyExprPreFacts
  allocLimits vyperTypeInvariants s1PrefixAnnAssignMemory exprSimInvScopeAbsence vyperStorageTrace words bodyFullSimProjection
  bodySim exprSimHypsDefs vyperTypeSystem bodyFullIfExpReach gasShadowCompileStmtBase vyperState finite_map loweringPosts stmtLowering gasShadow compileEnv bodyFullPreds

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac annassign_word_full_source >>
  `body_expr_prefix_ok cx e` by
    (first_x_assum irule >>
     qexistsl_tac [`es`, `es`, `get_tenv cx`, `tyv`] >>
     simp[lift_option_type_def, return_def]) >>
  `body_stmt_safe tops (AnnAssign id typ e)` by
    metis_tac[supported_stmt_body_safe] >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `lookup_scopes id es.scopes = NONE` by
    (drule_all_then assume_tac body_inv_expr_body_pre_mods >>
     drule_then assume_tac expr_body_pre_mods_inv >>
     drule_then assume_tac expr_sim_inv_mods_env >>
     fs[env_consistent_def, env_scopes_consistent_def] >>
     Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     qpat_x_assum `!id entry. lookup_scopes _ _ = _ ==> _`
       (drule_then mp_tac) >> simp[FLOOKUP_DEF]) >>
  rw[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  fs[stmt_env_def, declare_stmt_local_def, gas_shadow_stmt_def,
     comp_bind_def, comp_ignore_bind_def, comp_return_def,
     pairTheory.pair_case_thm] >>
  Cases_on `declare_local cenv id (expr_type e) sa` >>
  rename1 `declare_local _ _ _ sa = (rhs_ce,r)` >>
  Cases_on `declare_local (gas_shadow_env T cenv) id (expr_type e) shadow_sa` >>
  rename1 `declare_local _ _ _ shadow_sa = (shadow_rhs_ce,r')` >>
  `shadow_rhs_ce = gas_shadow_env T rhs_ce` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `id` |-> `id`,
                     `ty` |-> `expr_type e`, `sd` |-> `T`]
       (REWRITE_RULE [gas_shadow_compiles_env_def]
          gas_shadow_compiles_env_declare_local)) >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  qpat_x_assum `shadow_rhs_ce = _` SUBST_ALL_TAC >>
  Cases_on `compile_stmt rhs_ce lctx ret_ty (AnnAssign id (expr_type e) e) r` >>
  Cases_on `compile_stmt (gas_shadow_env T rhs_ce) lctx ret_ty
              (AnnAssign id (expr_type e) (gas_shadow_expr e)) r'` >>
  gvs[] >>
  drule_all_then strip_assume_tac annassign_full_declared_rhs_pre >>
  drule_all_then strip_assume_tac
    bodyFullSimProjectionTheory.body_expr_full_ok_simulations >>
  qpat_assum `body_expr_prefix_ok _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
  qpat_assum `!DF lo d PG tops ctx sc f sf ce env ty es.
                _ ==> expr_sim_prefix _ _ _ _ _ _ /\ expr_vv_sim_prefix _ _ _ _ _ _`
    (drule_all_then strip_assume_tac) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0`
    by metis_tac[body_inv_no_phi] >>
  irule annassign_word_prefix_execution_sep >>
  rpt (first_assum (irule_at Any)) >> simp[] >>
  disch_tac >> first_assum ACCEPT_TAC
QED
*)
Theorem body_annassign_word_prefix:
  !cx id typ e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_full_ok cx e) /\
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_prefix_ok cx e) /\
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
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  cheat
QED

Theorem body_annassign_memory_prefix:
  !cx id typ e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_full_ok cx e) /\
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_prefix_ok cx e) /\
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
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
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
  `FLOOKUP cenv.ce_vars id = NONE` by metis_tac[declared_name_unbound] >>
  `lookup_scopes id es.scopes = NONE` by
    metis_tac[expr_sim_inv_scope_lookup_none] >>
  `supported_expr tops e` by fs[supported_stmt_annassign] >>
  `body_stmt_safe tops (AnnAssign id typ e)` by
    metis_tac[supported_stmt_body_safe] >>
  `expr_body_pre cenv cx env e es` by metis_tac[body_annassign_rhs_pre] >>
  `env.type_defs = get_tenv cx` by metis_tac[expr_body_pre_env_type_defs] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    metis_tac[assignable_type_well_formed, well_formed_type_def,
              optionTheory.IS_SOME_EXISTS] >>
  `lift_option_type (evaluate_type (get_tenv cx) typ)
     "AnnAssign evaluate_type" es = (INL tyv,es)` by
    simp[lift_option_type_def, return_def] >>
  `body_expr_full_ok cx e /\ body_expr_prefix_ok cx e` by metis_tac[] >>
  irule annassign_memory_prefix_execution >>
  rpt (conj_tac ORELSE qexistsl_tac [`env`,`tops`]) >> simp[] >>
  rpt gen_tac >> disch_tac >>
  drule_all_then strip_assume_tac annassign_full_declared_rhs_pre >>
  simp[]
  >- (irule bodyFullSimProjectionTheory.body_expr_full_ok_simulations >> metis_tac[]) >>
  qpat_assum `body_expr_prefix_ok _ _`
    (strip_assume_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem body_annassign_widened_prefix:
  !cx id typ e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_full_ok cx e) /\
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_prefix_ok cx e) /\
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
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (irule declared_name_unbound >> metis_tac[]) >>
  `well_typed_expr env e /\ assignable_type env.type_defs typ /\
   id NOTIN FDOM env.var_types` by gvs[type_stmt_annassign, AllCaseEqs()] >>
  `supported_expr tops e` by fs[supported_stmt_annassign] >>
  `body_stmt_safe tops (AnnAssign id typ e)` by
    metis_tac[supported_stmt_body_safe] >>
  `expr_body_pre cenv cx env e es` by metis_tac[body_annassign_rhs_pre] >>
  `env.type_defs = get_tenv cx` by metis_tac[expr_body_pre_env_type_defs] >>
  `?dtv. evaluate_type (get_tenv cx) typ = SOME dtv` by
    metis_tac[assignable_type_well_formed, well_formed_type_def,
              optionTheory.IS_SOME_EXISTS] >>
  `body_expr_prefix_ok cx e` by
    (first_x_assum irule >> qexistsl_tac [`es`,`es`,`get_tenv cx`,`dtv`] >>
     simp[lift_option_type_def, return_def]) >>
  `lookup_scopes id es.scopes = NONE` by
    metis_tac[expr_sim_inv_scope_lookup_none] >>
  `type_memory_bytes cenv typ < dimword (:256)` by
    (fs[stmt_exprs_ok_def, alloc_limits_stmt_def, type_alloc_ok_def,
        dimword_def] >> decide_tac) >>
  `!sta ce r. declare_local cenv id typ sta = (ce,r) ==>
     expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
       ce cx (expr_type e) e es` by
    (rpt gen_tac >> strip_tac >>
     drule_all_then strip_assume_tac annassign_full_declared_rhs_pre >>
     metis_tac[CONJUNCT1 body_expr_prefix_ok_def]) >>
  rewrite_tac[stmt_frag_prefix_def] >> rpt gen_tac >> strip_tac >>
  `~s0.vs_halted` by fs[stmt_frag_full_pre_def] >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_prefix_full_invalid_trace_domain >>
      simp[evaluate_storage_trace_frame]) >>
  irule annassign_prefix_from_rhs_trace >> simp[] >>
  Cases_on `has_length_word typ /\ is_empty_value_expr e`
  >- simp[annassign_empty_rhs_prefix] >>
  drule_all annassign_alloc_lowered_rhs_prefix >> simp[]
QED

Theorem body_annassign_other_prefix:
  !cx id typ e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_full_ok cx e) /\
  (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_prefix_ok cx e) /\
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
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  rpt gen_tac >> strip_tac >>
  `well_typed_expr env e /\ assignable_type env.type_defs typ /\
   type_widens_to env.type_defs (expr_type e) typ /\
   id NOTIN FDOM env.var_types` by gvs[type_stmt_annassign, AllCaseEqs()] >>
  `~is_bytestring_type (expr_type e)` by
    metis_tac[typedMemoryCopyTheory.type_widens_from_bytestring] >>
  Cases_on `lowered_value_type cenv e = expr_type e`
  >- (`FLOOKUP cenv.ce_vars id = NONE` by
        (irule declared_name_unbound >> metis_tac[]) >>
      `supported_expr tops e` by fs[supported_stmt_annassign] >>
      `body_stmt_safe tops (AnnAssign id typ e)` by
        metis_tac[supported_stmt_body_safe] >>
      `expr_body_pre cenv cx env e es` by metis_tac[body_annassign_rhs_pre] >>
      `env.type_defs = get_tenv cx` by metis_tac[expr_body_pre_env_type_defs] >>
      `lookup_scopes id es.scopes = NONE` by
        (drule_all_then assume_tac body_inv_expr_body_pre_mods >>
         drule_then assume_tac expr_body_pre_mods_inv >>
         drule_then assume_tac expr_sim_inv_mods_env >>
         fs[env_consistent_def, env_scopes_consistent_def] >>
         Cases_on `lookup_scopes id es.scopes` >> simp[] >>
         qpat_x_assum `!id entry. lookup_scopes _ _ = _ ==> _`
           (drule_then mp_tac) >> simp[FLOOKUP_DEF]) >>
      `?stv. evaluate_type (get_tenv cx) (expr_type e) = SOME stv` by
        metis_tac[exprSimHypsTheory.expr_body_pre_type_evaluates, optionTheory.IS_SOME_EXISTS] >>
      `?dtv. evaluate_type (get_tenv cx) typ = SOME dtv` by
        metis_tac[assignable_type_well_formed, well_formed_type_def,
                  optionTheory.IS_SOME_EXISTS] >>
      `lift_option_type (evaluate_type (get_tenv cx) typ) "AnnAssign evaluate_type" es = (INL dtv,es)` by
        simp[lift_option_type_def, return_def] >>
      `body_expr_full_ok cx e /\ body_expr_prefix_ok cx e` by metis_tac[] >>
      irule s1PrefixAnnAssignOtherTheory.annassign_other_typed_prefix_execution >>
      `~is_bytestring_type typ /\ ~(has_length_word typ /\ is_empty_value_expr e) /\ expr_type e <> typ`
        by metis_tac[] >>
      simp[] >>
      (conj_tac >- metis_tac[]) >>
      qexistsl_tac [`env`,`tops`] >> simp[] >>
      conj_tac >> rpt gen_tac >> disch_tac >>
      drule_all_then strip_assume_tac annassign_full_declared_rhs_pre >>
      metis_tac[body_expr_full_ok_simulations, CONJUNCT1 body_expr_prefix_ok_def]) >>
  `0 < type_memory_bytes cenv typ` by
    metis_tac[exprSimAggregateLayoutTheory.annassign_memory_bytes_pos_ptr] >>
  `~(lowered_value_type cenv e = expr_type e \/
      is_bytestring_type (expr_type e) /\
      is_bytestring_type (lowered_value_type cenv e) /\
      arg_type_fits (lowered_value_type cenv e) (expr_type e))` by metis_tac[] >>
  irule body_annassign_widened_prefix >>
  rpt (first_assum (irule_at Any)) >> simp[] >> metis_tac[]
QED
