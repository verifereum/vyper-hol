Theory bodyFullBopWordOperands
Ancestors
  bodyFullPreds bodySimFull exprSimOperators exprBopSimProps exprSimSource
  gasOutcomeFullCompose gasExemptCert gasStorage gasShadowState gasShadow
  bodyMemoryDefs exprLoweringProps loweringPosts bodyPtrDefs
  vyperStorageTrace vyperStorageFootprint vyperState compileEnv
  fragExec list exprSimDefs freshWrites contextRawReachable ptrDiscipline unitMemInv

Theorem bop_word_operands_full_cps:
  word_value_type (expr_type e1) /\ word_value_type (expr_type e2) /\
  body_exprs_full_ok cx [e1; e2] /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es /\
  lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
  lower_value compile_expr cenv (expr_type e1) e2 s1 = (y,s2) /\
  lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e1) shadow_sa =
    (x,shadow_s1) /\
  lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e2) shadow_s1 =
    (y,shadow_s2) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state s1 shadow_s1 /\
  gas_shadow_state s2 shadow_s2 /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
  fn_has_code shadow_sa shadow_s1 shadow_func /\
  fn_has_code shadow_s1 shadow_s2 shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= s1.cs_next_var /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!left v1 mid G1 tn1 t right v2 fin G2 tn2 u.
    (!tail. bind (eval_expr cx e1) (read_result cx)
      (es with gas_obs := gas_explicit left s0.vs_gas_readings ++ tail) =
      (INL v1, mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      (expr_post H ctx func cenv cx e1 es sa s1 s0 mid v1 x t /\
      expr_store_bound cx (expr_type e1) v1 x t /\
      t.vs_current_bb = s1.cs_current_bb /\
      t.vs_inst_idx = LENGTH s1.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
      ptr_val_ok cx (post_value_type cenv e1) v1 x G1 tn1 t /\
      (~is_word_type (post_value_type cenv e1) ==> ptr_buf_ok cenv e1 x G1 t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
      ~t.vs_halted /\ mid.gas_obs = [])) /\
    (!tail. bind (eval_expr cx e2) (read_result cx)
      (mid with gas_obs := gas_explicit right t.vs_gas_readings ++ tail) =
      (INL v2, fin with gas_obs := tail)) /\
    storage_trace_domain cx st0 fin.storage_trace /\
    (!H. valid_horizon cx st0 H fin.storage_trace ==>
      (expr_post H ctx func cenv cx e2 mid s1 s2 t fin v2 y u /\
      expr_store_bound cx (expr_type e2) v2 y u /\
      u.vs_current_bb = s2.cs_current_bb /\
      u.vs_inst_idx = LENGTH s2.cs_current_insts /\
      alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx fin G2 tn2 u /\
      ptr_val_ok cx (post_value_type cenv e2) v2 y G2 tn2 u /\
      (~is_word_type (post_value_type cenv e2) ==> ptr_buf_ok cenv e2 y G2 u) /\
      ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2 /\
      ~u.vs_halted /\ fin.gas_obs = [])) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0
      (\ee. (bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 ee, ee))
      (fin,u,G2,tn2) Q (\H res ee gt r. expr_exit res r)) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (bind (eval_expr cx (Builtin ann (Bop bop) [e1; e2])) (read_result cx))
    (es,s0,G0,tn0) Q (\H res ee gt r. expr_exit res r)
Proof
  qabbrev_tac `P = (\e es ca cb t0 G0 tn0 op H (res : value + vyperState$exception) ee G tn t.
    ?v. res = INL v /\
      expr_post H ctx func cenv cx e es ca cb t0 ee v op t /\
      expr_store_bound cx (expr_type e) v op t /\
      t.vs_current_bb = cb.cs_current_bb /\
      t.vs_inst_idx = LENGTH cb.cs_current_insts /\
      alloca_history func t /\ t0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
      ghost_kept_at lo cenv es ca G0 tn0 t0 G tn /\
      ~t.vs_halted /\ ee.gas_obs = [])` >> strip_tac >>
  drule expr_body_pre_bop >> strip_tac >>
  `is_word_type (expr_type e1) /\ is_word_type (expr_type e2)` by
    metis_tac[word_value_type_word] >>
  `!start fn inst s. frag_reachable ctx func start fn inst s ==>
    dalloca_no_wrap inst s` by
    (rpt strip_tac >> drule frag_reachable_members >>
     disch_then drule >> strip_tac >>
     fs[ctx_has_dalloca_def, EXISTS_MEM, dalloca_no_wrap_def] >>
     metis_tac[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e1) e1 es` by
    (gvs[body_exprs_full_ok_def] >>
     metis_tac[body_expr_full_ok_def]) >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ e1 _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `s1`, `shadow_sa`, `shadow_s1`, `x`,
    `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  rewrite_tac[REWRITE_RULE [ETA_THM] eval_expr_bop_bind] >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt (pop_assum kall_tac) >> rpt strip_tac >>
      irule gas_exempt_cert_bind_value >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (rpt (pop_assum kall_tac) >> gen_tac >> BETA_TAC >>
      irule storage_trace_frame_bind_all >> conj_tac
      >- simp[storage_trace_frame_def, exprBopSimDefsTheory.bop_result_def] >>
      irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  qexists_tac `P e1 es sa s1 s0 G0 tn0 x` >> reverse conj_tac
  >- (BETA_TAC >> irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[Abbr `P`] >> rpt strip_tac >>
      Cases_on `res` >> gvs[expr_exit_def]) >>
  qx_genl_tac [`left`, `res`, `mid`, `G1`, `tn1`, `t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (P = _)`
    (fn th => simp[REWRITE_RULE [markerTheory.Abbrev_def] th, NoAsms]) >>
  strip_tac >> gvs[] >>
  `mid with gas_obs := [] = mid` by
    simp[evaluation_state_component_equality] >>
  qpat_assum `!tail. bind _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `expr_sim_inv cenv cx env mid` by
    (drule_at (Pos last) (REWRITE_RULE [ETA_THM] expr_body_pre_eval) >>
     disch_then (qspec_then `cenv` mp_tac) >>
     simp[] >> metis_tac[]) >>
  `expr_body_pre cenv cx env e2 mid` by metis_tac[] >>
  `body_expr_full_ok cx e2` by
    (gvs[body_exprs_full_ok_def] >> first_x_assum irule >>
     qpat_x_assum `bind (eval_expr cx e1) _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e1) e2 mid` by metis_tac[body_expr_full_ok_def] >>
  `local_ptrs_reserved cenv s1` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z)` by
    metis_tac[not_fresh_at_mono] >>
  `return_buf_frame d cenv s1 t` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp[Abbr `P`, expr_post_def, NoAsms] >> strip_tac >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e2) (read_result cx)) expr_res_ok mid` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ e2 _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `s1`, `s2`, `shadow_s1`, `shadow_s2`, `y`,
    `t`, `G1`, `tn1`] mp_tac) >>
  (impl_tac >- (gvs[Abbr `P`, expr_post_def] >> metis_tac[])) >> strip_tac >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt (pop_assum kall_tac) >> rpt strip_tac >>
      irule gas_exempt_cert_bind_value >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >>
      simp[storage_trace_frame_def, exprBopSimDefsTheory.bop_result_def]) >>
  qexists_tac `P e2 mid s1 s2 t G1 tn1 y` >> reverse conj_tac
  >- (BETA_TAC >> irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[Abbr `P`] >> rpt strip_tac >>
      Cases_on `res` >> gvs[expr_exit_def]) >>
  qx_genl_tac [`right`, `res2`, `fin`, `G2`, `tn2`, `u`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace)
     fin.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
    (qspec_then `storage_trace_horizon fin.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (P = _)`
    (fn th => simp[REWRITE_RULE [markerTheory.Abbrev_def] th, NoAsms]) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `!left v1 mid G1 tn1 t right v2 fin G2 tn2 u. _`
    (qspecl_then [`left`, `v`, `mid`, `G1`, `tn1`, `t`,
                 `right`, `v'`, `fin`, `G2`, `tn2`, `u`] mp_tac) >>
  fs[Abbr `P`] >> metis_tac[]
QED
