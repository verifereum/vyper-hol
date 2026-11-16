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
  bodySimDeclCases bodyFullAnnAssignMemoryPost bodyFullMemoryValue
  bodyFullAnnAssignReserve bodyFullPathHistory bodyFullPathFrontier
  bodyFullAnnAssignCompose gasOutcomeFullStmts annassignRelayoutFrag
  annassignRelayoutSource annassignRelayoutPost bodyExprPreFacts
  supportedStmtTraverse supportedExprs supportedExprTraverse vyperTypeEnv
  vyperTypeInvariants vyperTypeContractStaticMaps supportedDecls compileVyper
  gasContext exprSimSource exprSimHyps assignRelayoutCaller allocLimits
  vyperTypeCallGraph bodyInvNoDalloca

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

val _ = Parse.hide "body";

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
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  `body_stmt_safe tops (AnnAssign id typ e)` by
    metis_tac[supported_stmt_body_safe] >>
  `well_typed_expr env e /\ assignable_type env.type_defs typ /\
   type_widens_to env.type_defs (expr_type e) typ /\
   id NOTIN FDOM env.var_types` by gvs[type_stmt_def, AllCaseEqs()] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    metis_tac[assignable_type_well_formed, well_formed_type_def,
              optionTheory.IS_SOME_EXISTS] >>
  `body_expr_full_ok cx e` by
    (first_x_assum irule >>
     qexistsl_tac [`es`, `es`, `get_tenv cx`, `tyv`] >>
     simp[lift_option_type_def, return_def]) >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  `cx_tops cx = tops` by
    (irule cx_tops_module >> fs[body_inv_def]) >>
  `~supported_expr_exists (const_name_root cx) e` by
    metis_tac[body_inv_const_name_free] >>
  `expr_body_pre cenv cx env e es` by
    (irule (Q.INST [`calls` |-> `[]`] (SPEC_ALL stmt_expr_body_pre)) >>
     fs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
        int_calls_stmt_def, int_calls_expr_def] >>
     drule supported_expr_body_calls >> strip_tac >>
     fs[body_inv_def] >> metis_tac[]) >>
  drule_all assign_relayout_source_classify >> strip_tac >>
  `type_memory_bytes cenv typ < 2 ** 64` by
    gvs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  drule_all widening_memory_layout_bound >> strip_tac >>
  `~(has_length_word typ /\ is_empty_value_expr e)` by
    (Cases_on `e` >>
     gvs[is_empty_value_expr_def, exprLoweringTheory.lowered_value_type_def, expr_type_def]) >>
  rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_initial_domain >>
  simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >> strip_tac >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  drule_all annassign_relayout_code_parts >> strip_tac >>
  rename1 `declare_local cenv id typ sa = (cenv',st)` >>
  `FLOOKUP cenv.ce_vars id = NONE` by
    (fs[ce_locals_declared_def] >> Cases_on `FLOOKUP cenv.ce_vars id` >>
     gvs[] >> metis_tac[FLOOKUP_DEF]) >>
  `lookup_scopes id es.scopes = NONE` by
    (Cases_on `lookup_scopes id es.scopes` >> simp[] >>
     gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     res_tac >> gvs[FLOOKUP_DEF]) >>
  `?H0. valid_horizon cx st0 H0 es.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `stmt_state_rel H0 ctx func cenv cx es s0 /\
   ghost_inv_at (DF H0) lo d cenv cx es G0 tn0 s0` by metis_tac[] >>
  `allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by
    fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `fn_has_code sa sA func` by
    (drule_all stmtSimPropsTheory.declare_local_ptr >> strip_tac >>
     gvs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def]) >>
  `type_memory_bytes cenv typ < dimword (:256)` by
    (gvs[wordsTheory.dimword_def] >> decide_tac) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[loweringPostsTheory.ret_pc_ok_def] >>
  drule_all (Q.INST_TYPE [`:'a` |-> `:256`, `:'b` |-> `:256`] body_full_declared_alloc_path) >>
  disch_then (qspecl_then [`tn0`,`gas_explicit_sites ctx shadow_ctx`,`PG`,`G0`] strip_assume_tac) >>
  `same_frame cenv cenv'` by
    (drule_then irule declare_local_same_frame >> simp[]) >>
  `body_inv tops ctx cenv' cx` by metis_tac[body_inv_same_frame] >>
  `expr_sim_inv cenv' cx env es` by
    (irule expr_sim_inv_declare_local >> goal_assum (drule_at Any) >> simp[]) >>
  `stmt_exprs_ok cenv' (AnnAssign id typ e)` by
    (drule_all annassign_declare_exprs_ok >> simp[]) >>
  `expr_body_pre cenv' cx env e es` by
    (irule (Q.INST [`calls` |-> `[]`] (SPEC_ALL stmt_expr_body_pre)) >>
     fs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
        int_calls_stmt_def, int_calls_expr_def] >>
     drule supported_expr_body_calls >> strip_tac >>
     fs[body_inv_def] >> metis_tac[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv' cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_full_ok cx e`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_full_ok_def]) >>
     disch_then drule_all >> simp[]) >>
  `?shadow_st. declare_local cenv id typ shadow_sa = (cenv',shadow_st) /\
    gas_shadow_state st shadow_st` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `id` |-> `id`, `ty` |-> `typ`]
      gasShadowCompileStmtBaseTheory.gas_shadow_compiles_declare_local) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[] >>
     Cases_on `declare_local cenv id typ shadow_sa` >> gvs[]) >>
  `?shadow_sA. emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv typ))] [p]
      shadow_st = ((),shadow_sA) /\ gas_shadow_state sA shadow_sA` by
    (mp_tac (Q.INST [`opc` |-> `ALLOCA`,
       `ops` |-> `[Lit (n2w (type_memory_bytes cenv typ))]`, `outs` |-> `[p]`]
       gasShadowStateTheory.gas_shadow_compiles_emit_inst) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`st`,`shadow_st`] mp_tac) >> simp[] >>
     Cases_on `emit_inst ALLOCA [Lit (n2w (type_memory_bytes cenv typ))] [p] shadow_st` >> gvs[]) >>
  `?shadow_sB. lower_value compile_expr cenv' (expr_type e) (gas_shadow_expr e)
      shadow_sA = (op,shadow_sB) /\ gas_shadow_state sB shadow_sB` by
    (mp_tac (Q.INST [`cenv` |-> `cenv'`, `ty` |-> `expr_type e`, `e` |-> `e`]
      gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sA`,`shadow_sA`] mp_tac) >> simp[] >>
     Cases_on `lower_value compile_expr cenv' (expr_type e) (gas_shadow_expr e) shadow_sA` >> simp[]) >>
  `local_ptrs_reserved cenv shadow_sa` by
    (qpat_assum `gas_shadow_state sa shadow_sa` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[gasShadowStateTheory.gas_shadow_state_def,
          loweringStateRelDefsTheory.local_ptrs_reserved_def,
          loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]) >>
  `fn_has_code shadow_sA shadow_sB shadow_func` by
    (qpat_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     pure_rewrite_tac[gas_shadow_stmt_def] >> strip_tac >>
     qpat_x_assum `stmt_env _ _ _ (AnnAssign _ _ e) sa = _` kall_tac >>
     `~(has_length_word typ /\ is_empty_value_expr (gas_shadow_expr e))` by
       (Cases_on `e` >> gvs[is_empty_value_expr_def, gas_shadow_expr_def]) >>
     drule_all annassign_relayout_code_parts >> strip_tac >> gvs[]) >>
  `alloca_inv s0` by
    (qpat_assum `stmt_state_rel H0 _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[exprLoweringPropsTheory.stmt_state_rel_def]) >>
  `alloca_history func u` by
    (irule body_full_path_alloca_history >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `!fn inst s. frag_reachable ctx func u fn inst s ==> dalloca_no_wrap inst s` by
    (rpt strip_tac >> drule_all contextRawReachableTheory.frag_reachable_members >> strip_tac >>
     fs[ptrDisciplineTheory.ctx_has_dalloca_def, EXISTS_MEM, unitMemInvTheory.dalloca_no_wrap_def] >> metis_tac[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sA`,`sB`,`shadow_sA`,`shadow_sB`,`op`,
    `u`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- (simp[] >>
    rpt conj_tac
    >- (`cenv'.ce_is_ctor = cenv.ce_is_ctor` by
          metis_tac[bodyPtrDefsTheory.same_frame_is_ctor] >>
        qpat_assum `!H. dead_lo_ok _ _ _ _ _` mp_tac >>
        pure_rewrite_tac[bodyPtrDefsTheory.dead_lo_ok_def] >>
        metis_tac[])
    >- (rpt strip_tac >>
        `cenv'.ce_return_buf = cenv.ce_return_buf` by
          (qpat_assum `same_frame cenv cenv'` mp_tac >>
           rpt (pop_assum kall_tac) >>
           simp[same_frame_def, compile_env_component_equality]) >>
        metis_tac[])
    >- (rpt strip_tac >>
        `cenv'.ce_return_pc = cenv.ce_return_pc` by
          (qpat_assum `same_frame cenv cenv'` mp_tac >>
           rpt (pop_assum kall_tac) >>
           simp[same_frame_def, compile_env_component_equality]) >>
        metis_tac[])
    >- (irule stmtSimDeclSourceTheory.annassign_admissible_rhs >> metis_tac[])
    >- (`s0.vs_alloca_next <= u.vs_alloca_next` by
          (irule body_full_path_alloca_next_mono >> metis_tac[]) >>
        `cenv'.ce_return_buf = cenv.ce_return_buf` by
          (qpat_assum `same_frame cenv cenv'` mp_tac >>
           rpt (pop_assum kall_tac) >>
           simp[same_frame_def, compile_env_component_equality]) >>
        qpat_assum `return_buf_frame d cenv sa s0` mp_tac >>
        qpat_assum `cenv'.ce_return_buf = cenv.ce_return_buf` mp_tac >>
        qpat_assum `s0.vs_alloca_next <= u.vs_alloca_next` mp_tac >>
        qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sA x` mp_tac >>
        qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _` mp_tac >>
        rpt (pop_assum kall_tac) >> rpt strip_tac >>
        Cases_on `d` >- gvs[loweringPostsTheory.return_buf_frame_def] >>
        PairCases_on `x` >> gvs[loweringPostsTheory.return_buf_frame_def] >>
        metis_tac[arithmeticTheory.LESS_EQ_TRANS])
    >- metis_tac[]
    >> rpt strip_tac >>
       qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
         (qspec_then `H` mp_tac) >>
       (impl_tac >- simp[]) >> strip_tac >>
       first_assum irule >> simp[])) >>
  strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule gasOutcomeFullStmtsTheory.gas_outcome_full_zero_prefix >>
  qexistsl_tac [`G1`,`u`,`tn1`] >>
  conj_tac >- simp[] >>
  qpat_x_assum `cx_tops cx = tops` (SUBST1_TAC o SYM) >>
  irule annassign_full_outcome >>
  conj_tac >- (qexists_tac `lctx` >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []`, `childR`, `tyv`] >>
  conj_tac
  >- (simp[Abbr `childR`, bodyPtrDefsTheory.stmt_exit_ptr_def] >>
      rpt (pop_assum kall_tac) >> rpt gen_tac >> strip_tac >>
      Cases_on `res` >- gvs[exprSimDefsTheory.expr_exit_def] >>
      Cases_on `r` >> Cases_on `y` >>
      gvs[exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >>
      gvs[exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def]) >>
  conj_tac >- suspend "memory_continue" >>
  conj_tac >- (simp[Abbr `childQ`] >> metis_tac[]) >>
  conj_tac >- simp[] >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >> simp[]
QED

Resume body_annassign_widened_full[memory_continue]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
    mid.storage_trace` by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qunabbrev_tac `childQ` >> rule_assum_tac BETA_RULE >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `INL v = INL _` (SUBST_ALL_TAC o REWRITE_RULE [sumTheory.INL_11]) >>
  `value_has_type stv v' /\ value_has_type tyv v' /\
   val_wf stv v' /\ val_wf tyv v' /\
   val_footprint stv v' = type_memory_size stv` by
    (qpat_assum `!tail. bind _ _ _ = _`
       (assume_tac o SRULE [] o Q.SPEC `[]`) >>
     irule (SRULE [SF ETA_ss] annassign_relayout_read_layout) >>
     goal_assum (drule_at (Pat `bind _ _ _ = _`)) >>
     qexistsl_tac [`cenv`,`env`,`tops`,`typ`] >> fs[body_inv_def]) >>
  `cenv'.ce_struct_fields = cenv.ce_struct_fields /\
   cenv'.ce_func_return_type = cenv.ce_func_return_type` by
    (qpat_assum `same_frame cenv cenv'` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[same_frame_def,compile_env_component_equality]) >>
  `lowered_value_type cenv' e = lowered_value_type cenv e` by
    (irule allocLimitsPropsTheory.lowered_value_type_frame >> simp[]) >>
  `post_value_type cenv' e = lowered_value_type cenv e` by
    (qpat_assum `post_value_type cenv e = _` mp_tac >>
     qpat_assum `lowered_value_type cenv' e = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `e` >>
     fs[loweringPostsTheory.post_value_type_def] >>
     rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
     fs[loweringPostsTheory.post_value_type_def]) >>
  `st.cs_next_id < sA.cs_next_id` by
    (qpat_assum `emit_inst _ _ _ st = _`
       (mp_tac o MATCH_MP emitHelperPropsTheory.emit_inst_extends) >> simp[]) >>
  drule expr_post_reserved_destination_source >>
  disch_then (qspecl_then [`lowered_value_type cenv e`,`stv`,
    `st.cs_next_id`,`b`,`type_memory_bytes cenv typ`,`b`,
    `type_memory_bytes cenv typ`,`p`,`n2w b`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `sw` assume_tac) >>
  RULE_L_ASSUM_TAC CONJUNCTS >>
  rename1 `ptr_val_ok cx (post_value_type cenv' e) v' op Gi ti u'` >>
  `0 < type_memory_size stv` by
    (irule strict_widening_source_positive >>
     qexistsl_tac [`expr_type e`,`lowered_value_type cenv e`,`get_tenv cx`] >> simp[]) >>
  qpat_assum `ptr_val_ok _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ptr_val_ok_def]) >>
  simp[] >> disch_then (mp_tac o CONJUNCT2) >>
  rewrite_tac[bodyPtrDefsTheory.ptr_mem_ok_def] >>
  disch_then (qspecl_then [`stv`,`sw`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `val_footprint stv v' <> 0` by simp[] >>
  qpat_x_assum `val_footprint _ _ <> 0 ==> _` drule >>
  disch_then (qx_choosel_then [`xs`,`srcbase`,`n`] strip_assume_tac) >>
  qpat_x_assum `op = Var xs` SUBST_ALL_TAC >>
  `lookup_var xs u' = SOME sw` by fs[venomStateTheory.eval_operand_def] >>
  `val_store_size stv v' = type_memory_size stv` by
    (`!ty tv v. ~is_bytestring_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv ==>
        val_store_size tv v = type_memory_size tv` suffices_by metis_tac[] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     Cases_on `v` >> simp[exprSimPropsTheory.val_store_size_def] >>
     Cases_on `tv` >> simp[] >> rename1 `BaseTV bt` >> Cases_on `bt` >> simp[] >>
     Cases_on `ty` >>
     gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), is_bytestring_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), is_bytestring_type_def]) >>
  `ptr_covers Gi ti xs u' (type_memory_size stv)` by
    (simp[bodyPtrDefsTheory.ptr_covers_def] >>
     metis_tac[bodyPtrDefsTheory.ptr_val_ok_def]) >>
  `ptr_covers Gi ti p u' (type_memory_size tyv)` by
    (qpat_assum `ptr_covers G1 tn1 p u _` mp_tac >>
     qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `lookup_var p u' = _` mp_tac >>
     qpat_assum `lookup_var p u = _` mp_tac >>
     qpat_assum `not_fresh_at sA p` mp_tac >>
     qpat_assum `type_memory_bytes cenv typ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[bodyPtrDefsTheory.ghost_kept_at_def,bodyPtrDefsTheory.ptr_covers_def] >>
     metis_tac[]) >>
  `allocas_from lo u' /\ lo <= u'.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ mid Gi ti u'` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def] >> metis_tac[]) >>
  `expr_val_at cenv' cx (lowered_value_type cenv e) sA sB mid v' (Var xs) u'` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ mid v' _ u'`
       (mp_tac o List.nth o (fn th => (CONJUNCTS th,3)) o
        REWRITE_RULE [loweringPostsTheory.expr_post_def]) >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace)
     ctx func cenv' cx mid u'` by fs[loweringPostsTheory.expr_post_def] >>
  `!i. w2n sw <= i /\ i < w2n sw + val_footprint stv v' ==>
     i < u'.vs_alloca_next` by
    (qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `stmt_state_rel _ _ _ _ _ mid u'` mp_tac >>
     qpat_assum `evaluate_type _ (lowered_value_type cenv e) = _` mp_tac >>
     qpat_assum `~is_word_type (lowered_value_type cenv e)` mp_tac >>
     qpat_assum `eval_operand (Var xs) u' = SOME sw` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     metis_tac[allocationPtrTheory.expr_val_at_below_frontier]) >>
  `w2n sw + type_memory_size stv <= u'.vs_alloca_next` by
    (qpat_x_assum `!i. _ ==> i < u'.vs_alloca_next`
       (qspec_then `w2n sw + type_memory_size stv - 1` mp_tac) >>
     simp[] >> decide_tac) >>
  `alloca_inv u'` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ mid u'` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[exprLoweringPropsTheory.stmt_state_rel_def]) >>
  `b + type_memory_size tyv <= u'.vs_alloca_next` by
    (qpat_assum `alloca_inv u'` mp_tac >>
     qpat_assum `FLOOKUP u'.vs_allocas _ = _` mp_tac >>
     qpat_assum `type_memory_bytes cenv typ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[venomMemDefsTheory.alloca_inv_def,venomMemDefsTheory.alloca_next_valid_def]) >>
  `sA.cs_next_var <= sB.cs_next_var` by fs[exprLoweringPropsTheory.ci_mono_def] >>
  `local_ptrs_reserved cenv' sB` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sA` >> simp[]) >>
  `not_fresh_at sB p` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `not_fresh_at sB xs` by
    (drule_then (drule_then assume_tac) exprOperandVarTheory.compile_lower_value_var >> simp[]) >>
  drule_at (Pos hd) residual_call_compile_location >>
  disch_then (qspecl_then [`expr_type e`,`sA`,`vv`,`sV`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cenv'.ce_return_buf = cenv.ce_return_buf /\
   cenv'.ce_return_pc = cenv.ce_return_pc` by
    (qpat_assum `same_frame cenv cenv'` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[bodySimTheory.same_frame_def] >>
     disch_then (mp_tac o CONJUNCT1) >>
     disch_then (fn th => mp_tac (AP_TERM ``\c. (c.ce_return_buf,c.ce_return_pc)`` th)) >> simp[]) >>
  `(!x cap. cenv'.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sB x) /\
   (!x cap. cenv'.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sB x)` by
    (simp[] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `!ty. type_memory_bytes cenv' ty = type_memory_bytes cenv ty` by
    (gen_tac >> irule compileEnvTheory.type_memory_bytes_struct_fields >> simp[]) >>
  qpat_assum `body_inv _ _ cenv' _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [body_inv_def]) >>
  qpat_assum `expr_sim_inv cenv' _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_sim_inv_def]) >>
  `b < dimword (:256)` by
    (qpat_assum `b + type_memory_bytes cenv typ < _` mp_tac >>
     rpt (pop_assum kall_tac) >> decide_tac) >>
  `st.cs_next_id <> sB.cs_next_id` by
    (qpat_assum `ci_mono sA sB` mp_tac >>
     qpat_assum `st.cs_next_id < sA.cs_next_id` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  qpat_assum `stmt_state_rel _ _ _ _ _ mid u'`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac
      (Q.INST_TYPE [`:'a` |-> `:256`, `:'b` |-> `:256`]
        bodyFullMemoryValueTheory.body_full_memory_value_path)) >>
  disch_then drule >>
  disch_then (drule_at (Pat `lookup_var p u' = SOME _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ (lowered_value_type cenv e) = SOME _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ typ = SOME _`)) >>
  disch_then (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ xs u' _`)) >>
  disch_then (qspecl_then [`lo`,`gas_explicit_sites ctx shadow_ctx`,`(n2w b):bytes32`,`PG`] mp_tac) >>
  (impl_tac >- (simp[] >> disj2_tac >>
    qexistsl [`st.cs_next_id`,`type_memory_size tyv`] >> simp[])) >>
  disch_then (qx_choosel_then [`t`,`Gf`,`tf`,`us`,`Gu`,`tu`,`scStore`]
    (map_every assume_tac o CONJUNCTS)) >>
  `not_fresh_at scStore p` by
    (qpat_assum `ci_mono sB scStore` mp_tac >>
     qpat_assum `not_fresh_at sB p` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `ptr_covers Gu tu p us (type_memory_size tyv)` by
    (irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl_tac [`Gi`,`u'`,`ti`] >> simp[] >>
     qpat_assum `!x. not_fresh_at scStore x ==> _` (qspec_then `p` mp_tac) >>
     qpat_assum `!x. not_fresh_at sB x ==> _` (qspec_then `p` mp_tac) >> simp[]) >>
  `us.vs_allocas = t.vs_allocas` by
    (qpat_assum `typed_copy_state_frame _ _ _ us t` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[typedMemoryCopyTheory.typed_copy_state_frame_def,
          venomStateTheory.venom_state_component_equality] >> metis_tac[]) >>
  `FLOOKUP us.vs_allocas st.cs_next_id = SOME (b,type_memory_bytes cenv typ)` by
    metis_tac[] >>
  drule_all stmtSimDeclSourceTheory.annassign_continuation_all_tails >>
  disch_then (qx_choosel_then [`sc`,`rest`] strip_assume_tac) >>
  qexistsl [`mid with scopes :=
    (sc |+ (id,<|assignable := T; type := tyv; value := v'; popped := []|>)) :: rest`,
    `t`,`Gf`,`tf`] >>
  simp[] >> qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `stmt_state_rel H ctx func cenv' cx mid u'` by
    (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[loweringPostsTheory.expr_post_def]) >>
  `stmt_state_rel H ctx func cenv' cx mid us /\
   ghost_inv_at (DF H) lo d cenv' cx mid Gu tu us` by
    (conj_tac >> first_assum irule >> simp[]) >>
  `stmt_state_rel H ctx func cenv' cx
     (mid with scopes := (sc |+ (id,<|assignable := T; type := tyv; value := v'; popped := []|>)) :: rest) t /\
   ghost_inv_at (DF H) lo d cenv' cx
     (mid with scopes := (sc |+ (id,<|assignable := T; type := tyv; value := v'; popped := []|>)) :: rest) Gf tf t` by
    (irule bodyFullAnnAssignMemoryPostTheory.body_full_annassign_memory_post >>
     simp[] >> conj_tac >- (qexists_tac `sb` >> simp[]) >>
     qexistsl_tac [`Gu`,`PG`,`(n2w b):bytes32`,
       `gas_explicit_sites ctx shadow_ctx`,
       `mk_inst st.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv typ))] [p]`,
       `us`,`scStore`,`tu`] >> simp[] >>
     rpt conj_tac
     >- metis_tac[exprLoweringPropsTheory.ci_mono_def,
          freshWritesTheory.not_fresh_at_mono]
     >- metis_tac[exprLoweringPropsTheory.ci_mono_def,
          freshWritesTheory.not_fresh_at_mono]
     >- (rpt strip_tac >>
         metis_tac[exprSimOperandsTheory.fresh_not_local_ptr,
           exprLoweringPropsTheory.local_ptrs_reserved_next_var,
           exprLoweringPropsTheory.ci_mono_def])
     >- (simp[venomInstTheory.mk_inst_def] >> metis_tac[]) >>
     irule exprLoweringPropsTheory.local_ptrs_reserved_not_live >>
     conj_tac >- (qexistsl_tac [`id`,`type_memory_bytes cenv typ`] >> metis_tac[]) >>
     qexists_tac `sB` >> simp[]) >>
  simp[loweringPostsTheory.stmt_lands_def] >>
  conj_tac
  >- (qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      qpat_assum `unwrap_value _ _ _ = _` mp_tac >>
      qpat_assum `~block_is_terminated sV` mp_tac >>
      qpat_assum `acyclic_struct_metadata _` mp_tac >>
      rpt (pop_assum kall_tac) >>
      metis_tac[stmtSimDeclTypedCodeTheory.compile_assign_value_typed_open,
         exprOpenTerminalsTheory.unwrap_value_open]) >>
  conj_tac
  >- (irule stmtSimDeclComposeTheory.cenv_top_ext_declare_local >>
      simp[] >> qexistsl_tac [`id`,`sa`,`st`,`typ`] >> simp[] >>
      qpat_assum `lookup_scopes id mid.scopes = NONE` mp_tac >>
      qpat_assum `mid.scopes = sc::rest` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[vyperStateTheory.lookup_scopes_def] >>
      Cases_on `FLOOKUP sc id` >> simp[]) >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[vyperStateTheory.evaluation_state_component_equality]) >>
  once_rewrite_tac[GSYM vyperStateTheory.evaluation_state_fupdcanon] >>
  simp[] >> conj_tac
  >- (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[loweringPostsTheory.expr_post_def,
           vyperStorageFootprintTheory.storage_well_formed_on_def] >>
      strip_tac >> rpt gen_tac >> Cases_on `b` >>
      fs[vyperStorageBackendTheory.get_storage_def] >>
      metis_tac[vyperStorageBackendTheory.get_storage_def]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
          lookup_var x t = SOME w` by
    (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `!x. not_fresh_at sB x ==> lookup_var x t = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sA x` mp_tac >>
     qpat_assum `sA.cs_next_var <= sB.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[loweringPostsTheory.expr_post_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by
    (irule body_full_path_alloca_next_mono >> metis_tac[]) >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by
    (qpat_assum `s0.vs_alloca_next <= u.vs_alloca_next` mp_tac >>
     qpat_assum `u.vs_alloca_next <= u'.vs_alloca_next` mp_tac >>
     qpat_assum `u'.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
     rpt (pop_assum kall_tac) >> decide_tac) >>
  conj_tac
  >- (qpat_assum `return_buf_frame d cenv sa s0` mp_tac >>
      qpat_assum `cenv'.ce_return_buf = cenv.ce_return_buf` mp_tac >>
      qpat_assum `s0.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
      qpat_assum `!x w. not_fresh_at sa x /\ _ ==> lookup_var x t = _` mp_tac >>
      qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sA x` mp_tac >>
      qpat_assum `ci_mono sA sB` mp_tac >>
      qpat_assum `ci_mono sB sb` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[exprLoweringPropsTheory.ci_mono_def] >> rpt strip_tac >>
      Cases_on `d` >- gvs[loweringPostsTheory.return_buf_frame_def] >>
      PairCases_on `x` >> gvs[loweringPostsTheory.return_buf_frame_def] >>
      metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  asm_rewrite_tac[] >> conj_tac
  >- (qpat_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      qpat_assum `!aid ent. FLOOKUP u'.vs_allocas aid = SOME ent ==> _` mp_tac >>
      qpat_assum `!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> _` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[loweringPostsTheory.expr_post_def] >> metis_tac[]) >>
  qpat_assum `ghost_kept_at lo cenv' es sA G1 tn1 u Gi ti` mp_tac >>
  qpat_assum `!x. not_fresh_at sB x ==> lookup_var x t = _ /\ _` mp_tac >>
  qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _` mp_tac >>
  qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at sA x` mp_tac >>
  qpat_assum `sA.cs_next_var <= sB.cs_next_var` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[bodyPtrDefsTheory.ghost_kept_at_def] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Finalise body_annassign_widened_full

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
