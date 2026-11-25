Theory entryCreateBopBytestringHandoff
Ancestors
  s1PrefixDefs bodyFullPreds bodyFullConvertEndpointPosts
  bodyFullIfExpReach bodyFullHashKeccakFixed bodyMemoryDefs
  exprSimSource exprSimHypsDefs exprLoweringProps freshWrites loweringPosts
  vyperStorageBackend vyperStorageTrace vyperStorageFootprint
  gasSummary gasExplicitSites

Triviality bytestring_read_storage_gas_obs:
  storage_well_formed_on cx (es with gas_obs := gs) regions <=>
  storage_well_formed_on cx es regions
Proof
  `!b. get_storage cx (es with gas_obs := gs) b = get_storage cx es b` by
    (Cases >> simp[get_storage_def]) >>
  simp[storage_well_formed_on_def]
QED

Theorem bop_bytestring_read_state_handoff:
  expr_body_pre cenv cx env e es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gs ++ tail) = (INL v,mid with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       storage_well_formed_on cx es (FST H)) ==>
  expr_sim_inv cenv cx env mid /\
  body_const_cells_agree [(NONE,tops)] cx env mid /\
  (?s tv t s1 w t1. eval_expr cx e s = (INL tv,t) /\
                    read_result cx tv s1 = (INL w,t1)) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace /\
       storage_well_formed_on cx mid (FST H))
Proof
  strip_tac >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` (assume_tac o SRULE [])) >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  conj_tac
  >- (drule_all (REWRITE_RULE [ETA_AX] exprSimSourceTheory.expr_body_pre_eval) >> simp[]) >>
  conj_tac
  >- (`well_typed_expr env e` by fs[expr_body_pre_def] >>
      `body_const_cells_agree [(NONE,tops)] cx env (mid with gas_obs := [])`
        suffices_by simp[] >>
      irule body_const_cells_agree_expr_read >>
      qpat_assum `bind _ _ _ = _` (irule_at Any) >> simp[]) >>
  conj_tac
  >- (drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> metis_tac[]) >>
  rpt strip_tac >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `bind _ _ _ = _` (mp_then Any mp_tac valid_horizon_frame) >>
     simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_read_result]) >> simp[] >>
  `storage_well_formed_on cx (mid with gas_obs := []) (FST H)`
    suffices_by simp[bytestring_read_storage_gas_obs] >>
  irule dynamic_read_storage_well_formed >>
  qpat_assum `bind _ _ _ = _` (irule_at Any) >>
  simp[bytestring_read_storage_gas_obs] >> metis_tac[]
QED

(* The hash post supplies the machine facts for either form of the second
   digest. Only the nonfolded branch has a compiled value-child interval. *)
Theorem bop_bytestring_second_start:
  expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann (Bop bop) [e1;e2]) es
    (st0,sa,sb,shadow_sa,shadow_sb,op,s0,G0,tn0) /\
  body_inv tops ctx cenv cx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  (!tail. bind (eval_expr cx e1) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL v,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s0,G0,tn0) marks (OK t,G1,tn1) /\
    stmt_state_rel H ctx func cenv cx mid t /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t) /\
  ~t.vs_halted /\ t.vs_current_bb = sh1.cs_current_bb /\
  t.vs_inst_idx = LENGTH sh1.cs_current_insts /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  wb_frame cenv es mid sa s0 t /\
  sa.cs_next_var <= sh1.cs_next_var /\ gas_shadow_state sh1 shadow_sh1 ==>
  expr_body_pre cenv cx env e2 mid /\
  body_const_cells_agree [(NONE,tops)] cx env mid /\
  (?s tv u s1 w t1. eval_expr cx e1 s = (INL tv,u) /\
                    read_result cx tv s1 = (INL w,t1)) /\
  local_ptrs_reserved cenv sh1 /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sh1 x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sh1 x) /\
  return_buf_frame d cenv sh1 t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t) /\
  (!m cb shadow_cb.
    bytestring_literal_hash e2 = NONE /\
    lower_value compile_expr cenv (expr_type e2) e2 sh1 = (m,cb) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e2)
      (gas_shadow_expr e2) shadow_sh1 = (m,shadow_cb) /\
    gas_shadow_state cb shadow_cb /\
    fn_has_code sh1 cb func /\ fn_has_code shadow_sh1 shadow_cb shadow_func ==>
    expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e2) e2 mid (st0,sh1,cb,shadow_sh1,shadow_cb,m,t,G1,tn1))
Proof
  simp[expr_sim_full_pre_def] >> strip_tac >>
  `expr_body_pre cenv cx env e1 es` by
    (irule expr_body_pre_builtin_arg >> conj_tac >- fs[expr_body_pre_def] >>
     qexistsl_tac [`ann`, `[e1;e2]`, `Bop bop`, `es`] >> simp[]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
       storage_well_formed_on cx es (FST H)` by metis_tac[] >>
  drule_all bop_bytestring_read_state_handoff >> strip_tac >>
  `expr_body_pre cenv cx env e2 mid` by
    (irule expr_body_pre_builtin_arg >> simp[] >>
     qexistsl_tac [`ann`, `[e1;e2]`, `Bop bop`, `es`] >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e2) (read_result cx)) expr_res_ok mid` by
    (irule expr_body_pre_gas_admissible >> goal_assum (drule_at Any)) >>
  `local_ptrs_reserved cenv sh1` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sh1 x` by
    metis_tac[not_fresh_at_mono] >>
  `!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sh1 x` by
    metis_tac[not_fresh_at_mono] >>
  `return_buf_frame d cenv sh1 t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >>
     fs[wb_frame_def]) >>
  qpat_x_assum `storage_trace_domain _ _ _` (assume_tac o REWRITE_RULE [storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule stmt_state_rel_allocas_below_fmp >> strip_tac >>
  `!bb. MEM bb func.fn_blocks ==>
       venomExecSemantics$phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx` mp_tac >>
     qpat_assum `MEM func ctx.ctx_functions` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi]) >>
  `!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u` by
    (qpat_assum `gas_origin_ptr_path _ _ _ (OK t,G1,tn1)` mp_tac >>
     qpat_assum `!bb. MEM bb func.fn_blocks ==> _` mp_tac >>
     qpat_assum `!fn inst u. frag_reachable ctx func s0 fn inst u ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\ storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by metis_tac[] >>
  simp[expr_sim_full_pre_def] >> metis_tac[]
QED
