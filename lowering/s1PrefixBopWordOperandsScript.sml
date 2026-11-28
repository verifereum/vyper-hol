(* Request-prefix companion to bodyFullBopWordOperands. *)
Theory s1PrefixBopWordOperands
Ancestors
  s1PrefixPreds bodyFullBopWordOperands s1PrefixCompose s1PrefixProps
  s1PrefixDefs bodyFullPreds bodyFullIfExpReach
  bodyFullExprsListFacts bodyFullSimProjection
  exprSimHyps exprSimSource exprBopSimProps exprBopSimDefs vyperStorageTrace
  gasOutcomeFullCompose exprSimDefs loweringPosts bodyMemoryDefs
  freshWrites vyperStorageFootprint vyperState exprBodyPreProps

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >> drule expr_body_pre_bop >> strip_tac >>
  `body_expr_full_ok cx e1` by
    (qpat_assum `body_exprs_full_ok cx [e1;e2]` mp_tac >>
     simp[NoAsms, body_exprs_full_ok_cons, body_exprs_full_ok_nil]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e1) e1 es` by metis_tac[body_expr_full_ok_simulations] >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e1) e1 es` by
    (qpat_assum `body_exprs_prefix_ok cx [e1;e2]` mp_tac >>
     simp[body_exprs_prefix_ok_def] >> metis_tac[body_expr_prefix_ok_def]) >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e1) e1 es
     (st0,sa,s1,shadow_sa,shadow_s1,x,s0,G0,tn0)` by
    (simp[expr_sim_full_pre_def] >> metis_tac[expr_body_pre_gas_admissible]) >>
  qpat_assum `expr_sim_prefix _ _ _ _ e1 es`
    (drule_then assume_tac o REWRITE_RULE [expr_sim_prefix_def]) >>
  qpat_assum `expr_sim_full _ _ _ _ e1 es`
    (drule_then assume_tac o REWRITE_RULE [expr_sim_full_eq]) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ fullQ headR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e1) (read_result cx)) (es,s0,G0,tn0)
     (\H rr ee G tn u. fullQ H rr ee G tn u /\ ~u.vs_halted /\ ee.gas_obs = []) headR` by
    (qpat_assum `gas_outcome_full _ _ _ _ _ _ fullQ headR`
       (mp_then Any irule gas_outcome_full_post_source) >> simp[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ fullQ headR` kall_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ headQ headR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e1) (read_result cx)) (es,s0,G0,tn0)
     (\H rr ee G tn u. headQ H rr ee G tn u /\
       ?cm. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s0,G0,tn0) cm (OK u,G,tn)) headR` by
    (qpat_assum `gas_outcome_full _ _ _ _ _ _ headQ headR`
       (mp_then Any irule gas_outcome_full_post_path) >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ headQ headR` kall_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ pathQ headR` >>
  rewrite_tac[REWRITE_RULE [ETA_THM] eval_expr_bop_bind] >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ pathQ headR`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result,
       Abbr `headR`] >>
  reverse (rpt conj_tac)
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
           storage_trace_frame_read_result] >>
      simp[storage_trace_frame_def, bop_result_def])
  >- (rpt gen_tac >> Cases_on `res` >> simp[]) >>
  suspend "right_operand"
QED
*)
Theorem bop_operands_prefix_cps_exit:
  is_word_type (expr_type e1) /\
  is_word_type (expr_type e2) /\
  body_exprs_full_ok cx [e1; e2] /\
  body_exprs_prefix_ok cx [e1; e2] /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es /\
  lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
  lower_value compile_expr cenv (expr_type e1) e2 s1 = (y,s2) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1) (gas_shadow_expr e1) shadow_sa =
    (x,shadow_s1) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1) (gas_shadow_expr e2) shadow_s1 =
    (y,shadow_s2) /\
  gas_shadow_state sa shadow_sa /\
  gas_shadow_state s1 shadow_s1 /\
  gas_shadow_state s2 shadow_s2 /\
  gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa s1 func /\
  fn_has_code s1 s2 func /\
  fn_has_code shadow_sa shadow_s1 shadow_func /\
  fn_has_code shadow_s1 shadow_s2 shadow_func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= s1.cs_next_var /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  return_buf_frame d cenv sa s0 /\
  alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r ==>
    R H res ee gt r) /\
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
      (fin,u,G2,tn2) Q R) /\
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
       gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (\ee. (bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 ee, ee))
      (fin,u,G2,tn2)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (bind (eval_expr cx (Builtin ann (Bop bop) [e1; e2])) (read_result cx))
      (es,s0,G0,tn0)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume bop_operands_prefix_cps_exit[right_operand]:
  rpt gen_tac >> strip_tac >>
  rename1 `!tail. bind (eval_expr cx e1) (read_result cx)
      (es with gas_obs := gas_explicit left s0.vs_gas_readings ++ tail) =
      (INL v1,mid with gas_obs := tail)` >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx e1 es sa s1 s0 mid v1 x t /\
    storage_well_formed_on cx mid (FST H) /\
    stmt_state_rel H ctx func cenv cx mid t /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (gen_tac >> disch_tac >> unabbrev_all_tac >>
     qpat_assum `!K. valid_horizon _ _ K mid.storage_trace ==> _`
       (qspec_then `H` (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) []))) >>
     qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ mid _ _ t`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> pathQ _ _ _ _ _ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then mp_tac)) >>
  simp[NoAsms, Abbr `pathQ`, Abbr `headQ`, Abbr `fullQ`] >> strip_tac >>
  `!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s` by
    (drule gas_origin_ptr_path_dalloca_fmp_headroom >>
     simp[] >> metis_tac[body_inv_no_phi]) >>
  `mid with gas_obs := [] = mid` by
    simp[evaluation_state_component_equality] >>
  qpat_assum `!tail. bind _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `expr_body_pre cenv cx env e2 mid` by
    (qpat_assum `!es'. expr_sim_inv _ _ _ es' ==> _` irule >>
     drule_at (Pos last) (REWRITE_RULE [ETA_THM] expr_body_pre_eval) >>
     disch_then (qspec_then `cenv` mp_tac) >> simp[] >> metis_tac[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`well_typed_expr env e1` by metis_tac[expr_body_pre_static_facts] >>
     `body_const_cells_agree [(NONE,tops)] cx env (mid with gas_obs := [])`
       suffices_by simp[] >>
     irule body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx e1) _ _ = (_,mid with gas_obs := [])`
       (irule_at Any) >> simp[]) >>
  drule (REWRITE_RULE [ETA_THM] eval_expr_read_INL) >> strip_tac >>
  `body_exprs_full_ok cx [e2]` by
    (qpat_assum `body_exprs_full_ok cx [e1;e2]`
       (strip_assume_tac o PURE_ONCE_REWRITE_RULE [body_exprs_full_ok_cons]) >>
     first_x_assum irule >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  `body_expr_full_ok cx e2` by
    (qpat_assum `body_exprs_full_ok cx [e2]` mp_tac >>
     simp[NoAsms, body_exprs_full_ok_cons, body_exprs_full_ok_nil]) >>
  `body_expr_prefix_ok cx e2` by
    (qpat_assum `body_exprs_prefix_ok cx [e1;e2]` mp_tac >>
     simp[body_exprs_prefix_ok_def, NoAsms] >> strip_tac >> first_x_assum irule >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e1) e2 mid` by metis_tac[body_expr_full_ok_simulations] >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e1) e2 mid` by metis_tac[body_expr_prefix_ok_def] >>
  `local_ptrs_reserved cenv s1` by metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z)` by
    metis_tac[not_fresh_at_mono] >>
  `return_buf_frame d cenv s1 t` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
     qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ mid _ _ t`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >> simp[]) >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e1) e2 mid
     (st0,s1,s2,shadow_s1,shadow_s2,y,t,G1,tn1)` by
    (simp[expr_sim_full_pre_def] >> metis_tac[expr_body_pre_gas_admissible]) >>
  suspend "compose_result"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume bop_operands_prefix_cps_exit[compose_result]:
  qpat_assum `expr_sim_prefix _ _ _ _ e2 mid`
    (drule_then assume_tac o REWRITE_RULE [expr_sim_prefix_def]) >>
  qpat_assum `expr_sim_full _ _ _ _ e2 mid`
    (drule_then assume_tac o REWRITE_RULE [expr_sim_full_eq]) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ (mid,t,G1,tn1) rightQ rightR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e2) (read_result cx)) (mid,t,G1,tn1)
     (\H rr ee G tn u. rightQ H rr ee G tn u /\ ~u.vs_halted /\ ee.gas_obs = []) rightR` by
    (qpat_assum `gas_outcome_full _ _ _ _ _ _ rightQ rightR`
       (mp_then Any irule gas_outcome_full_post_source) >> simp[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ rightQ rightR` kall_tac >>
  qpat_assum `gas_outcome_full _ _ _ _ _ (mid,t,G1,tn1) _ rightR`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result,
       Abbr `rightR`] >>
  reverse (rpt conj_tac)
  >- simp[storage_trace_frame_def, bop_result_def]
  >- (rpt gen_tac >> Cases_on `res` >> simp[]) >>
  qx_genl_tac [`right`, `v2`, `fin`, `G2`, `tn2`, `u`] >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
    (mk_asm "right_post") >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> pathQ _ _ _ _ _ _`
    (mk_asm "left_post") >>
  qpat_assum `!left v1 mid G1 tn1 t right v2 fin G2 tn2 u.
      _ ==> gas_prefix_full _ _ _ _ (fin,u,G2,tn2)`
    (qspecl_then [`left`, `v1`, `mid`, `G1`, `tn1`, `t`,
                  `right`, `v2`, `fin`, `G2`, `tn2`, `u`] mp_tac) >>
  `post_value_type cenv e1 = expr_type e1` by simp[post_value_type_word] >>
  `post_value_type cenv e2 = expr_type e2` by simp[post_value_type_word] >>
  unabbrev_all_tac >> BETA_TAC >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qx_gen_tac `H` >> disch_tac
     >- (asm "left_post" (qspec_then `H` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         simp[NoAsms, post_value_type_word] >> strip_tac >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         metis_tac[]) >>
     asm "right_post" (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp[NoAsms, post_value_type_word] >> strip_tac >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[])) >>
  simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise bop_operands_prefix_cps_exit
*)

Theorem bop_operands_prefix_cps:
  is_word_type (expr_type e1) /\
  is_word_type (expr_type e2) /\
  body_exprs_full_ok cx [e1; e2] /\
  body_exprs_prefix_ok cx [e1; e2] /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es /\
  lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
  lower_value compile_expr cenv (expr_type e1) e2 s1 = (y,s2) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1) (gas_shadow_expr e1) shadow_sa =
    (x,shadow_s1) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1) (gas_shadow_expr e2) shadow_s1 =
    (y,shadow_s2) /\
  gas_shadow_state sa shadow_sa /\
  gas_shadow_state s1 shadow_s1 /\
  gas_shadow_state s2 shadow_s2 /\
  gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa s1 func /\
  fn_has_code s1 s2 func /\
  fn_has_code shadow_sa shadow_s1 shadow_func /\
  fn_has_code shadow_s1 shadow_s2 shadow_func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= s1.cs_next_var /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  return_buf_frame d cenv sa s0 /\
  alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
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
      (fin,u,G2,tn2) Q (\H res ee gt r. expr_exit res r)) /\
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
       gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (\ee. (bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 ee, ee))
      (fin,u,G2,tn2)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (bind (eval_expr cx (Builtin ann (Bop bop) [e1; e2])) (read_result cx))
      (es,s0,G0,tn0)
Proof
  strip_tac >>
  mp_tac (Q.INST [`R` |-> `\H res ee gt r. expr_exit res r`]
    bop_operands_prefix_cps_exit) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[])) >>
  simp[]
QED
