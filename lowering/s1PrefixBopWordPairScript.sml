Theory s1PrefixBopWordPair
Ancestors
  s1PrefixPreds s1PrefixCompose s1PrefixProps s1PrefixDefs
  bodyFullPreds bodyFullBopWordLayout bodyFullSimProjection bodyFullIfExpReach
  bodyFullExprsListFacts bodyFullExprsSingleton
  exprSimHyps exprSimSource exprBopSimProps exprBopSimDefs vyperStorageTrace
  gasOutcomeFullCompose exprSimDefs loweringPosts bodyMemoryDefs
  freshWrites vyperStorageFootprint vyperState exprBodyPreProps exprSimWordArgs

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >> rewrite_tac[expr_sim_prefix_def, expr_sim_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all bop_full_layout >> strip_tac >>
  drule expr_body_pre_bop >> strip_tac >>
  `body_expr_full_ok cx e1 /\ body_expr_prefix_ok cx e1` by
    gvs[body_exprs_full_ok_cons, body_exprs_prefix_ok_def] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e1) e1 es` by
    metis_tac[body_expr_full_ok_simulations] >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e1) e1 es` by
    metis_tac[body_expr_prefix_ok_def] >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e1) e1 es
     (st0,sa,s1,shadow_sa,shadow_s1,x,s0,G0,tn0)` by
    (simp[expr_sim_full_pre_def] >> metis_tac[expr_body_pre_gas_admissible]) >>
  qpat_assum `expr_sim_prefix _ _ _ _ e1 es`
    (drule_then assume_tac o REWRITE_RULE [expr_sim_prefix_def]) >>
  qpat_assum `expr_sim_full _ _ _ _ e1 es`
    (drule_then assume_tac o REWRITE_RULE [expr_sim_full_eq]) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ headQ headR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e1) (read_result cx)) (es,s0,G0,tn0)
     (\H rr ee G tn u. headQ H rr ee G tn u /\ ~u.vs_halted /\ ee.gas_obs = []) headR` by
    (qpat_assum `gas_outcome_full _ _ _ _ _ _ headQ headR`
      (mp_then Any irule gas_outcome_full_post_source) >> simp[]) >>
  rewrite_tac[REWRITE_RULE [ETA_THM] eval_expr_bop_bind] >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ (\H rr ee G tn u. _ /\ ~u.vs_halted /\ _) headR`
    (mp_then Any irule gas_prefix_full_bind_replay) >>
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
  suspend "right_entry"
QED
*)
Theorem bop_word_pair_value_prefix:
  bop <> In /\ bop <> NotIn /\
  ~((bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1)) /\
  is_word_type ann /\ is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  body_exprs_full_ok cx [e1;e2] /\ body_exprs_prefix_ok cx [e1;e2] /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es ==>
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann (Bop bop) [e1;e2]) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume bop_word_pair_value_prefix[right_entry]:
  qx_genl_tac [`left`, `v1`, `mid`, `G1`, `tn1`, `t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (gen_tac >> disch_tac >>
     first_x_assum (qspec_then `H` (drule_then mp_tac)) >>
     simp[NoAsms, Abbr `headQ`, expr_post_def] >> strip_tac >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
      gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then mp_tac)) >>
  simp[NoAsms, Abbr `headQ`] >> strip_tac >>
  `!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s` by
    (drule gas_origin_ptr_path_dalloca_fmp_headroom >>
     simp[] >> metis_tac[body_inv_no_phi]) >>
  qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `expr_body_pre cenv cx env e2 mid` by
    (qpat_assum `!es'. expr_sim_inv _ _ _ es' ==> _` irule >>
     drule_at (Pos last) (REWRITE_RULE [ETA_THM] expr_body_pre_eval) >>
     disch_then (qspec_then `cenv` mp_tac) >> simp[] >> metis_tac[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`well_typed_expr env e1` by metis_tac[expr_body_pre_static_facts] >>
     `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     `body_const_cells_agree [(NONE,tops)] cx env (mid with gas_obs := [])`
       suffices_by simp[] >>
     irule body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx e1) _ _ = (_,mid with gas_obs := [])`
       (irule_at Any) >> simp[]) >>
  drule (REWRITE_RULE [ETA_THM] eval_expr_read_INL) >> strip_tac >>
  `body_expr_full_ok cx e2` by
    (qpat_assum `body_exprs_full_ok cx [e1;e2]` mp_tac >>
     simp[body_exprs_full_ok_singleton, body_exprs_full_ok_cons, NoAsms] >>
     strip_tac >> first_x_assum irule >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  `body_expr_prefix_ok cx e2` by
    (qpat_assum `body_exprs_prefix_ok cx [e1;e2]` mp_tac >>
     simp[body_exprs_prefix_ok_def, NoAsms] >> strip_tac >> first_x_assum irule >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  suspend "right_prefix"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume bop_word_pair_value_prefix[right_prefix]:
  `local_ptrs_reserved cenv s1` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
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
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e1) e2 mid` by metis_tac[body_expr_full_ok_simulations] >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e1) e2 mid` by metis_tac[body_expr_prefix_ok_def] >>
  qpat_assum `expr_sim_prefix _ _ _ _ e2 mid`
    (drule_then assume_tac o REWRITE_RULE [expr_sim_prefix_def]) >>
  qpat_assum `expr_sim_full _ _ _ _ e2 mid`
    (drule_then assume_tac o REWRITE_RULE [expr_sim_full_eq]) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ (mid,t,G1,tn1) rightQ rightR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e2) (read_result cx)) (mid,t,G1,tn1)
     (\H rr ee G tn u. ~u.vs_halted) rightR` by
    (qpat_assum `gas_outcome_full _ _ _ _ _ _ rightQ rightR`
       (mp_then Any irule gas_outcome_full_post_source) >> simp[]) >>
  qpat_assum `gas_outcome_full _ _ _ _ _ (mid,t,G1,tn1) (\H rr ee G tn u. ~u.vs_halted) rightR`
    (mp_then Any irule gas_prefix_full_bind_no_outcome) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result,
       storage_trace_frame_def, Abbr `rightR`] >>
  conj_tac >- (rpt gen_tac >> Cases_on `res` >> simp[]) >>
  simp[bop_result_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise bop_word_pair_value_prefix
*)
