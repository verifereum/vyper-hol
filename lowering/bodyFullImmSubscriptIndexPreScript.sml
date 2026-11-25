(* Index readiness at the selected normal return of an immutable base. *)
Theory bodyFullImmSubscriptIndexPre
Ancestors
  bodyFullTargetDefs bodyFullPreds bodyFullShared bodyFullTargetRoots
  bodyFullIfExpReach tuplePlaceSourceHead bodySimAugPlaceLoad targetPlaceSim targetPlaceSimCases
  exprSimFullBundleProps exprSimDefs exprSimHypsDefs bodyMemoryDefs
  fragGasOriginPtr gasSummary gasOutcomeFull gasShadow gasShadowState
  gasExplicitSites gasContext loweringPosts fragExec freshWrites exprLoweringProps
  vyperInterpreter vyperState vyperStorageFootprint list

Theorem immutable_target_index_ready[local]:
  body_base_target_full_ok cx (SubscriptTarget bt e) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  target_indices_pre cenv cx env (SubscriptTarget bt e) /\
  IS_SOME (type_place_target env bt) /\
  eval_target_place cx bt (es with gas_obs := gs) =
    (INL (ImmutablePlace NONE id path),mid) ==>
  eval_base_place cx bt (es with gas_obs := gs) =
    (INL (PlaceR (ImmutablePlace NONE id path)),mid) /\
  body_const_cells_agree [(NONE,tops)] cx env mid /\
  expr_sim_inv cenv cx env mid /\
  expr_body_pre cenv cx env e mid /\
  body_expr_full_ok cx e
Proof
  strip_tac >> conj_asm1_tac
  >- (irule tuple_place_target_base_inversion >> simp[]) >>
  conj_tac
  >- (irule body_const_cells_agree_base >>
      qpat_assum `eval_base_place _ _ _ = _` (irule_at Any) >> simp[]) >>
  conj_asm1_tac
  >- (irule aug_place_target_inv >>
      qpat_assum `eval_target_place _ _ _ = _` (irule_at Any) >>
      fs[target_indices_pre_def]) >>
  conj_tac >- fs[target_indices_pre_def] >>
  fs[body_base_target_full_ok_def] >> first_x_assum irule >> metis_tac[]
QED

Theorem immutable_index_admissible[local]:
  immutable_root cx bt /\
  gas_admissible (eval_target_place cx (SubscriptTarget bt e)) target_place_res_ok es /\
  (!tail. eval_target_place cx bt (es with gas_obs := gs ++ tail) =
      (INL p, mid1 with gas_obs := tail)) ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid1
Proof
  strip_tac >>
  drule_then (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th,GSYM bind_assoc]))
    immutable_target_subscript_source >>
  simp[gas_admissible_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >> rename1 `INR ex` >>
  `target_place_res_ok (INR ex : place + exception)` suffices_by
    simp[target_place_res_ok_def,expr_res_ok_def] >>
  qpat_x_assum `gas_admissible _ _ es` (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
  disch_then (qspec_then `gs ++ gs'` mp_tac) >>
  qpat_assum `!tail. eval_target_place _ _ _ = _` (qspec_then `gs'` assume_tac) >>
  simp[Once bind_def] >> simp[Once bind_def] >> gvs[]
QED

Theorem immutable_subscript_index_pre:
  body_inv tops ctx cenv cx /\
  body_base_target_full_ok cx (SubscriptTarget bt e) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  target_indices_pre cenv cx env (SubscriptTarget bt e) /\
  immutable_root cx bt /\ IS_SOME (type_place_target env bt) /\
  lower_value compile_expr cenv (expr_type e) e sm = (iop,sn) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
    (gas_shadow_expr e) shadow_sm = (iop,shadow_sn) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sm,sn,shadow_sm,shadow_sn) /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  gas_admissible (eval_target_place cx (SubscriptTarget bt e)) target_place_res_ok es /\
  mid1.gas_obs = [] /\ ~t1.vs_halted /\
  storage_trace_domain cx st0 mid1.storage_trace /\
  (!tail. eval_target_place cx bt
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL (ImmutablePlace NONE id path), mid1 with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H mid1.storage_trace ==>
    imm_target_post H ctx func cenv cx es sa sm s0 mid1 id path bty rb t1 /\
    t1.vs_current_bb = sm.cs_current_bb /\ t1.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func t1 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t1) /\
    s0.vs_alloca_next <= t1.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx mid1 G1 tn1 t1 /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s0,G0,tn0) marks (OK t1,G1,tn1)) ==>
  eval_base_place cx bt (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL (PlaceR (ImmutablePlace NONE id path)),mid1) /\
  body_const_cells_agree [(NONE,tops)] cx env mid1 /\
  expr_sim_inv cenv cx env mid1 /\ expr_body_pre cenv cx env e mid1 /\
  body_expr_full_ok cx e /\
  expr_sim_full_hypotheses (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e mid1 (st0,sm,sn,shadow_sm,shadow_sn,iop,t1,G1,tn1)
Proof
  strip_tac >>
  `mid1 with gas_obs := [] = mid1` by simp[evaluation_state_component_equality] >>
  qpat_assum `!tail. eval_target_place _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE std_ss [APPEND_NIL])) >>
  drule_all_then strip_assume_tac immutable_target_index_ready >> simp[] >>
  `valid_horizon cx st0 (storage_trace_horizon mid1.storage_trace)
    mid1.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (fs[expr_sim_full_code_def] >> metis_tac[body_inv_no_phi]) >>
  `!fn inst s. frag_reachable ctx func t1 fn inst s ==> dalloca_fmp_headroom inst s` by
    (qpat_assum `gas_origin_ptr_path _ _ _ _` mp_tac >>
     qpat_assum `!bb. MEM bb func.fn_blocks ==> _` mp_tac >>
     qpat_assum `!fn inst s. frag_reachable ctx func s0 fn inst s ==> _` mp_tac >>
     metis_tac[gas_origin_ptr_path_dalloca_fmp_headroom]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid1` by
    (irule immutable_index_admissible >> simp[] >>
     qexistsl_tac [`bt`,`es`] >> simp[] >>
     qexistsl_tac [`gas_explicit marks s0.vs_gas_readings`,
                   `ImmutablePlace NONE id path`] >> simp[]) >>
  `return_buf_frame d cenv sm t1` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
     fs[imm_target_post_def]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  `!H. valid_horizon cx st0 H mid1.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid1 t1 /\
    storage_well_formed_on cx mid1 (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid1 G1 tn1 t1` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _`
       (drule_then strip_assume_tac) >> fs[imm_target_post_def]) >>
  simp[expr_sim_full_hypotheses_def] >> metis_tac[]
QED
