Theory s1PrefixAnnAssignAllocRhs
Ancestors
  s1PrefixDefs s1PrefixCompose bodyFullAnnAssignMemoryPost bodyFullIfExpReach
  bodyFullHashKeccakFixed bodyInvExecutionProps bodySim bodyPtrDefs stateRelProj
  vyperStorageTrace vyperStorageFootprint exprLoweringProps stmtSimDeclSource

(* The allocation emits no explicit gas mark. Only the lowered RHS is
   needed for the request-prefix obligation; no copy or store follows it here. *)
Theorem annassign_alloc_lowered_rhs_prefix:
  stmt_frag_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
    (eval_stmt cx (AnnAssign id typ e)) es
    (st0,sa,sf,shadow_sa,shadow_sf,s0,G0,tn0,ce) /\
  body_inv tops ctx cenv cx /\
  storage_trace_domain cx st0 es.storage_trace /\
  ~is_word_type typ /\ 0 < type_memory_bytes cenv typ /\
  type_memory_bytes cenv typ < dimword (:256) /\
  FLOOKUP cenv.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE /\
  ~(has_length_word typ /\ is_empty_value_expr e) /\
  (!sa' ce' r. declare_local cenv id typ sa' = (ce',r) ==>
    expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce' cx (expr_type e) e es)
  ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
Proof
  pure_rewrite_tac[stmt_frag_full_pre_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cenv.ce_alloca_locals` by metis_tac[body_inv_contract,contract_inv_alloca_locals] >>
  drule_all annassign_full_prefix_parts >>
  disch_then (qx_choosel_then
    [`r`,`shadow_r`,`p`,`sz`,`a`,`shadow_a`,`vv`,`sv`,`shadow_sv`,`op`,`b`,`shadow_b`]
    strip_assume_tac) >>
  qpat_x_assum `if _ then _ else _` mp_tac >> asm_rewrite_tac[] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0 /\
    s0.vs_alloca_next + pending_alloca_size func s0 <= w2n s0.vs_initial_fmp` by
    (strip_tac >> simp[] >>
     `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0` by
       metis_tac[] >>
     drule stmt_state_rel_fmp_room >> simp[fmp_room_def] >> decide_tac) >>
  `sz < dimword (:256)` by simp[] >>
  drule_all annassign_full_alloc_entry >>
  disch_then (qspecl_then [`PG`,`gas_explicit_sites ctx shadow_ctx`]
    (qx_choosel_then [`w`,`entry`,`Ga`,`tna`] strip_assume_tac)) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `!fn inst z. frag_reachable ctx func entry fn inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s0,G0,tn0) [] (OK entry,Ga,tna)`
       (qspec_then `ARB` assume_tac) >>
     drule gas_origin_ptr_path_dalloca_fmp_headroom >> simp[] >>
     metis_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp entry` by
    (strip_tac >>
     `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func ce cx es entry` by
       metis_tac[] >>
     drule_all_then ACCEPT_TAC stmt_state_rel_allocas_below_fmp) >>
  `ce.ce_is_ctor = cenv.ce_is_ctor /\ ce.ce_modules = cenv.ce_modules` by
    (qpat_assum `ce with <|ce_vars := _; ce_var_type := _;
                          ce_dynarray_capacity := _|> = cenv` mp_tac >>
     simp[compileEnvTheory.compile_env_component_equality]) >>
  `!H. dead_lo_ok H (DF H) lo ce cx` by
    (qpat_assum `!H. dead_lo_ok H (DF H) lo cenv cx`
       (mp_tac o REWRITE_RULE [dead_lo_ok_def]) >>
     simp[dead_lo_ok_def]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[annassign_admissible_rhs] >>
  irule gas_prefix_full_zero_prefix_guarded >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,storage_trace_frame_read_result] >>
  qexistsl_tac [`Ga`,`entry`,`tna`] >> conj_tac >- metis_tac[] >>
  qpat_x_assum `!x y z. declare_local _ _ _ x = (y,z) ==> _` drule >>
  rewrite_tac[expr_sim_prefix_def] >>
  disch_then (qspecl_then [`st0`,`a`,`b`,`shadow_a`,`shadow_b`,`op`,`entry`,`Ga`,`tna`] mp_tac) >>
  simp[expr_sim_full_pre_def] >> metis_tac[]
QED
