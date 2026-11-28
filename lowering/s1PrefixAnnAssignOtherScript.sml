(* Request-prefix companion to bodyFullAnnAssignOther. *)
Theory s1PrefixAnnAssignOther
Ancestors
  s1PrefixPreds bodyFullAnnAssignOther s1PrefixDefs s1PrefixCompose gasOutcomeFull bodySim
  bodyFullAnnAssignMemoryPost bodyFullIfExpReach bodyFullHashKeccakFixed
  bodyFullPreds stmtSimDeclSource allocLimits stateRelProj bodyFullExtCallPackingReady
  exprLoweringProps loweringPosts bodyPtrDefs fragGasOriginPtr
  vyperStorageTrace vyperStorageFootprint vyperState
  venomState compileEnv list

Theorem annassign_other_typed_prefix_execution:
  body_inv tops ctx cenv cx /\
  expr_sim_inv cenv cx env es /\
  FLOOKUP cenv.ce_vars id = NONE /\
  lookup_scopes id es.scopes = NONE /\
  env.type_defs = get_tenv cx /\
  type_widens_to env.type_defs (expr_type e) typ /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
  evaluate_type (get_tenv cx) typ = SOME dtv /\
  stmt_exprs_ok cenv (AnnAssign id typ e) /\
  lowered_value_type cenv e = expr_type e /\
  ~is_word_type typ /\
  expr_type e <> typ /\
  ~is_bytestring_type typ /\
  ~(has_length_word typ /\ is_empty_value_expr e) /\
  (!sa ce r ty. declare_local cenv id typ sa = (ce,r) ==>
    body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es) /\
  (!sa ce r ty. declare_local cenv id typ sa = (ce,r) ==>
    body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
    expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es /\
    expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es) ==>
  stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
    (eval_stmt cx (AnnAssign id typ e)) es
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  PURE_REWRITE_TAC[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `type_memory_bytes cenv typ < dimword (:256)` by
    (qpat_assum `stmt_exprs_ok cenv (AnnAssign id typ e)`
       (strip_assume_tac o PURE_REWRITE_RULE [stmt_exprs_ok_def, alloc_limits_stmt_def]) >>
     irule arithmeticTheory.LESS_TRANS >> qexists_tac `2 ** 64` >>
     simp[wordsTheory.dimword_def]) >>
  `storage_trace_frame (eval_stmt cx (AnnAssign id typ e))` by
    simp[evaluate_storage_trace_frame] >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- suspend "allocation" >>
  suspend "invalid_domain"
QED

Resume annassign_other_typed_prefix_execution[allocation]:
    drule_all annassign_full_prefix_parts >>
    disch_then (qx_choosel_then
      [`r`,`shadow_r`,`p`,`sz`,`a`,`shadow_a`,`vv`,`sv`,`shadow_sv`,`op`,`b`,`shadow_b`]
      strip_assume_tac) >>
    `ctx_has_dalloca ctx ==> allocas_below_fmp s0 /\
      s0.vs_alloca_next + pending_alloca_size func s0 <= w2n s0.vs_initial_fmp` by
      (disch_tac >> asm_rewrite_tac[] >>
       `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0` by
         metis_tac[storage_trace_domain_def] >>
       drule stmt_state_rel_fmp_room >> simp[fmp_room_def] >> decide_tac) >>
    `sz < dimword (:256)` by simp[] >>
    drule_all annassign_full_alloc_entry >>
    disch_then (qspecl_then [`PG`,`gas_explicit_sites ctx shadow_ctx`]
      (qx_choosel_then [`w`,`entry`,`Ga`,`tna`] strip_assume_tac)) >>
    qpat_x_assum `if _ then _ else _` mp_tac >> asm_rewrite_tac[] >>
    disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
    qpat_x_assum `!sa ce r ty. declare_local cenv id typ sa = (ce,r) ==> _`
      (drule_then (qspec_then `expr_type e` strip_assume_tac)) >>
    `!bb. MEM bb func.fn_blocks ==> venomExecSemantics$phi_prefix_length bb.bb_instructions = 0` by
      (drule_at (Pat `body_inv tops ctx cenv cx`) body_inv_no_phi >>
       disch_then (qspec_then `func` mp_tac) >> simp[]) >>
    `!fn inst z. frag_reachable ctx func entry fn inst z ==> dalloca_fmp_headroom inst z` by
      (qpat_assum `!D. gas_origin_ptr_path _ _ [] (OK entry,Ga,tna)`
         (qspec_then `ARB` (mp_tac o MATCH_MP
           (REWRITE_RULE [GSYM AND_IMP_INTRO] gas_origin_ptr_path_dalloca_fmp_headroom))) >>
       asm_rewrite_tac[]) >>
    `cenv'.ce_is_ctor = cenv.ce_is_ctor` by
      (qpat_assum `cenv' with <|ce_vars := _; ce_var_type := _; ce_dynarray_capacity := _|> = _` mp_tac >>
       simp[compile_env_component_equality]) >>
    `cenv'.ce_modules = cenv.ce_modules` by
      (qpat_assum `cenv' with <|ce_vars := _; ce_var_type := _; ce_dynarray_capacity := _|> = _`
         (mp_tac o Q.AP_TERM `\ce. ce.ce_modules`) >> simp[]) >>
    `!H. dead_lo_ok H (DF H) lo cenv' cx` by fs[dead_lo_ok_def] >>
    `ctx_has_dalloca ctx ==> allocas_below_fmp entry` by
      (`stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv' cx es entry` by
        metis_tac[storage_trace_domain_def] >>
       drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
    drule annassign_admissible_rhs >> disch_tac >>
    `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cx st0 (bind (eval_expr cx e) (read_result cx)) (es,entry,Ga,tna)` by
      (qpat_assum `expr_sim_prefix _ _ _ _ _ _` (mp_tac o REWRITE_RULE
         [expr_sim_prefix_def,expr_sim_full_pre_def]) >>
       disch_then (qspecl_then [`st0`,`a`,`b`,`shadow_a`,`shadow_b`,`op`,`entry`,`Ga`,`tna`] mp_tac) >>
       asm_rewrite_tac[]) >>
    suspend "rhs_request"
QED

Resume annassign_other_typed_prefix_execution[rhs_request]:
    `!ss. (SND (eval_stmt cx (AnnAssign id typ e) ss)).storage_trace =
          (SND (bind (eval_expr cx e) (read_result cx) ss)).storage_trace` by
      (drule eval_annassign_action >> disch_then (qspecl_then [`id`,`e`] SUBST1_TAC) >>
       gen_tac >> Cases_on `bind (eval_expr cx e) (read_result cx) ss` >>
       rename1 `_ = (r0,mid)` >> Cases_on `r0` >> simp[bind_def] >>
       Cases_on `lookup_scopes id mid.scopes = NONE` >> Cases_on `mid.scopes` >>
       simp[new_variable_def, get_scopes_def, set_scopes_def, type_check_def,
            bind_def, ignore_bind_def, assert_def, return_def, raise_def]) >>
    irule gas_prefix_full_zero_prefix_guarded >> asm_rewrite_tac[] >>
    qexistsl_tac [`Ga`,`entry`,`tna`] >> asm_rewrite_tac[] >>
    qpat_x_assum `gas_prefix_full _ _ _ (bind _ _) _`
      (qx_choose_then `marks` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) o
       REWRITE_RULE [gas_prefix_full_def]) >>
    rewrite_tac[gas_prefix_full_def] >> qexists_tac `marks` >>
    conj_tac >- first_assum ACCEPT_TAC >>
    rpt gen_tac >> strip_tac >>
    qmatch_asmsub_abbrev_tac `eval_stmt cx (AnnAssign id typ e) src_st` >>
    Cases_on `bind (eval_expr cx e) (read_result cx) src_st` >>
    rename1 `_ = (rhs_res,rhs_state)` >>
    qpat_x_assum `!ss. (SND (eval_stmt _ _ ss)).storage_trace = _`
      (qspec_then `src_st` mp_tac) >>
    asm_rewrite_tac[pairTheory.SND] >> strip_tac >>
    unabbrev_all_tac >>
    qpat_x_assum `!tail res ee obs_pre rq outcome sfx H. _ ==> request_site _ _ _ _ _ _ _`
      (qspecl_then [`tail`,`rhs_res`,`rhs_state`,`obs_pre`,`rq`,`outcome`,`sfx`,`H`] mp_tac) >>
    asm_rewrite_tac[] >> metis_tac[]
QED

Resume annassign_other_typed_prefix_execution[invalid_domain]:
  simp[gas_prefix_full_def] >> qexists_tac `[]` >> conj_tac
  >- (qexistsl_tac [`storage_trace_horizon es.storage_trace`, `func`, `PG`, `G0`, `tn0`, `s0`] >>
      simp[gas_origin_ptr_focus_nil]) >>
  rpt gen_tac >> strip_tac >>
  drule_all storage_trace_frame_prefix >> simp[] >> strip_tac >>
  `es.storage_trace ++ observations = obs_pre ++ StorageOutcome rq outcome :: sfx` by fs[] >>
  `TAKE (LENGTH es.storage_trace) obs_pre = es.storage_trace` by
    (qpat_assum `es.storage_trace ++ _ = obs_pre ++ _`
      (mp_tac o AP_TERM ``TAKE (LENGTH es.storage_trace) : storage_trace_event list -> storage_trace_event list``) >>
     simp[TAKE_APPEND1, TAKE_LENGTH_ID]) >>
  `obs_pre = es.storage_trace ++ DROP (LENGTH es.storage_trace) obs_pre` by metis_tac[TAKE_DROP] >>
  metis_tac[extcall_packing_observed_domain, storage_trace_domain_prefix]
QED

Finalise annassign_other_typed_prefix_execution
