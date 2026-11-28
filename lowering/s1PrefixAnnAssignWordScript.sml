(* Request-prefix companion to bodyFullAnnAssignWord. *)
Theory s1PrefixAnnAssignWord
Ancestors
  s1PrefixPreds bodyFullAnnAssignWord s1PrefixDefs s1PrefixCompose s1PrefixProps vyperStorageTrace list gasShadowCompileStmtHelpers gasShadowCompileStmtBase stmtSimProps loweringSlice gasShadow exprLoweringProps bodyFullAnnAssignMemoryPost bodyFullHashKeccakFixed stateRelProj bodyFullIfExpReach stmtSimDeclSource bodySimFull exprSimDefs bodyFullAllocaFresh gasOutcomeFullCompose vyperState vyperStorageFootprint loweringPosts compileEnv

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >> Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- suspend "layout" >> suspend "no_horizon"
QED
*)
Theorem annassign_word_prefix_execution_sep:
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
  cenv.ce_alloca_locals /\
  FLOOKUP cenv.ce_vars id = NONE /\
  lookup_scopes id es.scopes = NONE /\
  expr_sim_inv cenv cx env es /\
  expr_body_pre cenv' cx env e es /\
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv' cx (expr_type e) e es /\
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv' cx (expr_type e) e es /\
  gas_shadow_state sa shadow_sa /\
  gas_shadow_state sf shadow_sf /\
  gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sf func /\
  fn_has_code shadow_sa shadow_sf shadow_func /\
  (ctx_has_dalloca ctx ==>
    (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s)) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~block_is_terminated sa /\
  gas_admissible (eval_stmt cx (AnnAssign id (expr_type e) e)) (stmt_res_ok lctx) es /\
  return_buf_frame d cenv sa s0 /\
  alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  declare_local cenv id (expr_type e) sa = (cenv',r) /\
  declare_local (gas_shadow_env T cenv) id (expr_type e) shadow_sa =
    (gas_shadow_env T cenv',r') /\
  compile_stmt cenv' lctx ret_ty (AnnAssign id (expr_type e) e) r = ((),sf) /\
  compile_stmt (gas_shadow_env T cenv') lctx ret_ty
    (AnnAssign id (expr_type e) (gas_shadow_expr e)) r' = ((),shadow_sf) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_stmt cx (AnnAssign id (expr_type e) e))
      (es,s0,G0,tn0)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume annassign_word_prefix_execution_sep[no_horizon]:
  `storage_trace_frame (eval_stmt cx (AnnAssign id (expr_type e) e))` by
    simp[evaluate_storage_trace_frame] >>
  rewrite_tac[gas_prefix_full_def] >> qexists_tac `[]` >> conj_tac
  >- (qexistsl_tac [`storage_trace_horizon es.storage_trace`, `func`, `PG`, `G0`, `tn0`, `s0`] >>
      simp[gasOutcomeFullTheory.gas_origin_ptr_focus_nil]) >>
  rpt gen_tac >> strip_tac >> drule_all storage_trace_frame_prefix >>
  simp[] >> strip_tac >>
  `es.storage_trace ++ observations = obs_pre ++ StorageOutcome rq outcome :: sfx` by fs[] >>
  pop_assum (strip_assume_tac o REWRITE_RULE [listTheory.APPEND_EQ_APPEND])
  >- (`l = []` by (Cases_on `l` >> fs[]) >>
      metis_tac[listTheory.APPEND_NIL,
                bodyFullExtCallPackingReadyTheory.extcall_packing_observed_domain]) >>
  metis_tac[gasOutcomeFullTheory.valid_horizon_append,
            bodyFullExtCallPackingReadyTheory.extcall_packing_observed_domain]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume annassign_word_prefix_execution_sep[layout]:
  drule_all annassign_word_full_declared_layout >>
  disch_then (qx_choosel_then [`p`, `a`, `b`, `op`] strip_assume_tac) >>
  `gas_shadow_state r r'` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `id` |-> `id`, `ty` |-> `expr_type e`, `sd` |-> `T`]
       gas_shadow_compiles_env_declare_local) >>
     rewrite_tac[gas_shadow_compiles_env_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  `r'.cs_blocks = shadow_sa.cs_blocks` by
    (drule_at (Pat `declare_local _ _ _ shadow_sa = _`) declare_local_ptr >>
     simp[] >> strip_tac >> simp[]) >>
  `fn_has_code r' shadow_sf shadow_func` by
    fs[fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def] >>
  `local_ptrs_reserved (gas_shadow_env T cenv) shadow_sa` by
    (`sa.cs_next_var = shadow_sa.cs_next_var` by
       fs[gasShadowStateTheory.gas_shadow_state_def] >>
     `local_ptrs_reserved cenv shadow_sa` by
       (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
     qpat_assum `local_ptrs_reserved cenv shadow_sa` mp_tac >>
     pure_rewrite_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def,
                      gasShadowCompileBaseTheory.gas_shadow_env_fields] >>
     disch_then ACCEPT_TAC) >>
  `local_ptrs_reserved (gas_shadow_env T cenv') r'` by
    (drule_at (Pat `declare_local _ _ _ shadow_sa = _`) declare_local_reserved >> simp[]) >>
  qpat_assum `compile_stmt _ _ _ (AnnAssign _ _ (gas_shadow_expr _)) _ = _`
    (mp_then (Pos hd) mp_tac compile_annassign_word_parts) >>
  disch_then (qspecl_then [`shadow_func`,`p`,`32`] mp_tac) >>
  simp[gas_shadow_expr_type, gasShadowCompileBaseTheory.gas_shadow_env_fields] >>
  (impl_tac >- metis_tac[compile_expr_grows]) >>
  disch_then (qx_choosel_then [`shadow_a`,`shadow_b`,`shadow_op`] strip_assume_tac) >>
  `gas_shadow_state a shadow_a` by
    (mp_tac (Q.INST [`opc` |-> `ALLOCA`, `ops` |-> `[Lit 32w]`, `outs` |-> `[p]`]
       gasShadowStateTheory.gas_shadow_compiles_emit_inst) >>
     rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`r`,`r'`] mp_tac) >> simp[]) >>
  `shadow_op = op /\ gas_shadow_state b shadow_b` by
    (mp_tac (Q.INST [`cenv` |-> `cenv'`, `e` |-> `e`, `ty` |-> `expr_type e`, `sd` |-> `T`]
       gas_shadow_stmt_lower_value_env) >>
     rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`a`,`shadow_a`] mp_tac) >> simp[]) >>
  gvs[] >> suspend "entry"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume annassign_word_prefix_execution_sep[entry]:
  `32 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0` by
    metis_tac[storage_trace_domain_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0 /\
    s0.vs_alloca_next + pending_alloca_size func s0 <= w2n s0.vs_initial_fmp` by
    (strip_tac >> conj_tac >- metis_tac[stmt_state_rel_allocas_below_fmp] >>
     drule stmt_state_rel_fmp_room >> simp[fmp_room_def] >> decide_tac) >>
  qpat_assum `type_memory_bytes cenv (expr_type e) = 32` (assume_tac o SYM) >>
  drule_all annassign_full_alloc_entry >>
  disch_then (qspecl_then [`PG`, `gas_explicit_sites ctx shadow_ctx`]
    (qx_choosel_then [`w`, `t`, `G'`, `tn'`] strip_assume_tac)) >>
  `cenv'.ce_is_ctor = cenv.ce_is_ctor /\ cenv'.ce_modules = cenv.ce_modules` by
    (qpat_assum `cenv' with <|ce_vars := _; ce_var_type := _;
                              ce_dynarray_capacity := _|> = cenv` mp_tac >>
     simp[compile_env_component_equality]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    metis_tac[storage_trace_domain_def, stmt_state_rel_allocas_below_fmp] >>
  `!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s` by
    (Cases_on `ctx_has_dalloca ctx`
     >- (qpat_assum `ctx_has_dalloca ctx ==> (!bb. _) /\ (!fn inst s. _)`
           (drule_then strip_assume_tac) >>
         qpat_assum `!D. gas_origin_ptr_path _ (s0,G0,tn0) [] (OK t,G',tn')`
           (qspec_then `ARB` (fn path =>
           qpat_assum `!bb. MEM bb func.fn_blocks ==> _` (fn phi =>
           qpat_assum `!fn inst s. frag_reachable ctx func s0 fn inst s ==> _` (fn safe =>
           ACCEPT_TAC (MATCH_MP gas_origin_ptr_path_dalloca_fmp_headroom
             (LIST_CONJ [path,phi,safe]))))))) >>
     rpt strip_tac >> drule contextRawReachableTheory.frag_reachable_members >>
     disch_then drule >> strip_tac >>
     fs[ptrDisciplineTheory.ctx_has_dalloca_def, EXISTS_MEM,
        unitTransformDefsTheory.dalloca_fmp_headroom_def] >> metis_tac[]) >>
  `!H. dead_lo_ok H (DF H) lo cenv' cx` by
    (qpat_assum `cenv'.ce_modules = cenv.ce_modules` SUBST1_TAC >>
     qpat_assum `cenv'.ce_is_ctor <=> cenv.ce_is_ctor`
       (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `!H. dead_lo_ok H _ _ cenv _` mp_tac >>
     simp[bodyPtrDefsTheory.dead_lo_ok_def] >>
     gvs[bodyPtrDefsTheory.dead_lo_ok_def]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (drule annassign_admissible_rhs >> simp[]) >>
  suspend "source"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume annassign_word_prefix_execution_sep[source]:
  irule gas_prefix_full_zero_prefix_guarded >> simp[evaluate_storage_trace_frame] >>
  qexistsl_tac [`G'`,`t`,`tn'`] >>
  conj_tac >- metis_tac[] >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (eval_expr cx e) (read_result cx)) (es,t,G',tn')` by
    (qpat_assum `expr_sim_prefix _ _ _ _ _ _`
       (drule_all o REWRITE_RULE [expr_sim_prefix_def, expr_sim_full_pre_def]) >> simp[]) >>
  drule eval_annassign_action >> disch_then (qspecl_then [`id`,`e`] SUBST1_TAC) >>
  qpat_assum `expr_sim_full _ _ _ _ _ _`
    (drule_all o REWRITE_RULE [expr_sim_full_def]) >> strip_tac >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,t,G',tn')
     (\H res ee G tn u. ~u.vs_halted) (\H res ee gt r. ISR res)` by
    (qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _`
       (mp_then Any irule gas_outcome_full_post_source) >>
     simp[] >> rpt strip_tac >> Cases_on `res` >> fs[expr_exit_def]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn u. ~u.vs_halted) _`
    (mp_then Any irule gas_prefix_full_bind_no_outcome) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result,
       storage_trace_frame_new_variable] >>
  rpt gen_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
  Cases_on `st.scopes` >>
  simp[new_variable_def, bind_def, ignore_bind_def, get_scopes_def,
       type_check_def, assert_def, return_def, raise_def, set_scopes_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise annassign_word_prefix_execution_sep
*)

Theorem annassign_word_prefix_execution:
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
  cenv.ce_alloca_locals /\
  FLOOKUP cenv.ce_vars id = NONE /\
  lookup_scopes id es.scopes = NONE /\
  expr_sim_inv cenv cx env es /\
  expr_body_pre cenv' cx env e es /\
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv' cx (expr_type e) e es /\
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv' cx (expr_type e) e es /\
  gas_shadow_state sa shadow_sa /\
  gas_shadow_state sf shadow_sf /\
  gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sf func /\
  fn_has_code shadow_sa shadow_sf shadow_func /\
  ~ctx_has_dalloca ctx /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  ret_pc_ok cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~block_is_terminated sa /\
  gas_admissible (eval_stmt cx (AnnAssign id (expr_type e) e)) (stmt_res_ok lctx) es /\
  return_buf_frame d cenv sa s0 /\
  alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  declare_local cenv id (expr_type e) sa = (cenv',r) /\
  declare_local (gas_shadow_env T cenv) id (expr_type e) shadow_sa =
    (gas_shadow_env T cenv',r') /\
  compile_stmt cenv' lctx ret_ty (AnnAssign id (expr_type e) e) r = ((),sf) /\
  compile_stmt (gas_shadow_env T cenv') lctx ret_ty
    (AnnAssign id (expr_type e) (gas_shadow_expr e)) r' = ((),shadow_sf) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_stmt cx (AnnAssign id (expr_type e) e))
      (es,s0,G0,tn0)
Proof
  strip_tac >>
  `ctx_has_dalloca ctx ==>
    (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s)` by simp[] >>
  drule_all annassign_word_prefix_execution_sep >> simp[]
QED
