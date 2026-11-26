(* Request-prefix step for the two reached operands of scalar equality. *)
Theory s1PrefixBoolChainCompareStep
Ancestors
  s1PrefixCompose s1PrefixOfVV s1PrefixDefs s1PrefixProps bodyFullPreds bodyFullIfExpReach
  exprSimHyps exprSimSource exprBopSimProps exprBopSimDefs vyperStorageTrace
  gasOutcomeFullCompose exprSimDefs loweringPosts bodyMemoryDefs
  freshWrites vyperStorageFootprint vyperState exprLoweringProps exprBodyPreProps

Theorem bool_chain_compare_prefix_step:
  is_word_type (expr_type l) /\ expr_type r = expr_type l /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin (BaseT BoolT) (Bop Eq) [l;r]) es /\
  lower_value compile_expr cenv (expr_type l) l sa = (x,s1) /\
  lower_value compile_expr cenv (expr_type l) r s1 = (y,s2) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type l)
    (gas_shadow_expr l) shadow_sa = (x,shadow_s1) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type l)
    (gas_shadow_expr r) shadow_s1 = (y,shadow_s2) /\
  gas_shadow_state s1 shadow_s1 /\ gas_shadow_state s2 shadow_s2 /\
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
  fn_has_code shadow_sa shadow_s1 shadow_func /\
  fn_has_code shadow_s1 shadow_s2 shadow_func /\
  sa.cs_next_var <= s1.cs_next_var /\
  expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type l) l es (st0,sa,s1,shadow_sa,shadow_s1,x,s,G,tn) /\
  (body_const_cells_agree [(NONE,tops)] cx env es /\
   expr_body_pre cenv cx env l es /\
   expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type l) l es (st0,sa,s1,shadow_sa,shadow_s1,x,s,G,tn) ==>
   gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (bind (eval_expr cx l) (read_result cx)) (es,s,G,tn)
      (\H res ee G1 tn1 t. ?v. res = INL v /\
        expr_post H ctx func cenv cx l es sa s1 s ee v x t /\
        expr_store_bound cx (post_value_type cenv l) v x t /\
        t.vs_current_bb = s1.cs_current_bb /\
        t.vs_inst_idx = LENGTH s1.cs_current_insts /\
        alloca_history func t /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        s.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee G1 tn1 t /\
        ptr_val_ok cx (post_value_type cenv l) v x G1 tn1 t /\
        (~is_word_type (post_value_type cenv l) ==> ptr_buf_ok cenv l x G1 t) /\
        ghost_kept_at lo cenv es sa G tn s G1 tn1)
      (\H res ee gt q. expr_exit res q /\ halt_exit H cx ee res q /\
        (ctx_has_dalloca ctx ==> !u. q = Halt u ==> allocas_below_fmp u)) /\
   gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
      (bind (eval_expr cx l) (read_result cx)) (es,s,G,tn)) /\
  (!mid t G1 tn1.
   body_const_cells_agree [(NONE,tops)] cx env mid /\
   expr_body_pre cenv cx env r mid /\
   expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type l) r mid (st0,s1,s2,shadow_s1,shadow_s2,y,t,G1,tn1) ==>
   gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
      (bind (eval_expr cx r) (read_result cx)) (mid,t,G1,tn1)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
    (bind (eval_expr cx (Builtin (BaseT BoolT) (Bop Eq) [l;r])) (read_result cx))
    (es,s,G,tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule expr_body_pre_bop >> strip_tac >>
  qpat_x_assum `_ ==> gas_outcome_full _ _ _ _ _ _ _ _ /\ _`
    (drule_all_then strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ leftQ leftR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx l) (read_result cx)) (es,s,G,tn)
     (\H res ee G1 tn1 t. leftQ H res ee G1 tn1 t /\ ~t.vs_halted /\ ee.gas_obs = []) leftR` by
    (qpat_x_assum `gas_outcome_full _ _ _ _ _ _ leftQ leftR`
       (mp_then Any irule gas_outcome_full_post_source) >> simp[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ leftQ leftR` kall_tac >>
  rewrite_tac[REWRITE_RULE [ETA_THM] eval_expr_bop_bind] >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ leftR`
    (mp_then Any irule gas_prefix_full_bind_replay) >>
  simp[Abbr `leftR`, storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result] >>
  reverse (rpt conj_tac)
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
           storage_trace_frame_read_result] >>
      simp[storage_trace_frame_def, bop_result_def])
  >- (rpt gen_tac >> Cases_on `res` >> simp[]) >>
  suspend "right_entry"
QED

Resume bool_chain_compare_prefix_step[right_entry]:
  qx_genl_tac [`marks`,`v`,`mid`,`G1`,`tn1`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
        expr_post H ctx func cenv cx l es sa s1 s mid v x t /\
        ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!K. valid_horizon _ _ K mid.storage_trace ==> _`
       (qspec_then `H` (drule_then mp_tac)) >>
     simp[NoAsms, Abbr `leftQ`] >> strip_tac >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_x_assum `!K. valid_horizon _ _ K mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then mp_tac)) >>
  simp[NoAsms, Abbr `leftQ`] >> strip_tac >>
  qpat_x_assum `expr_sim_full_pre _ _ _ _ l es _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_full_pre_def]) >>
  `!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u` by
    (drule gas_origin_ptr_path_dalloca_fmp_headroom >> simp[] >> metis_tac[body_inv_no_phi]) >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  qpat_assum `!tail. bind _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `expr_body_pre cenv cx env r mid` by
    (qpat_assum `!es'. expr_sim_inv _ _ _ es' ==> _` irule >>
     drule_at (Pos last) (REWRITE_RULE [ETA_THM] expr_body_pre_eval) >>
     disch_then (qspec_then `cenv` mp_tac) >> simp[] >> metis_tac[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`well_typed_expr env l` by metis_tac[expr_body_pre_static_facts] >>
     `body_const_cells_agree [(NONE,tops)] cx env (mid with gas_obs := [])`
       suffices_by simp[] >>
     irule body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx l) _ _ = (_,mid with gas_obs := [])`
       (irule_at Any) >> simp[]) >>
  suspend "right_prefix"
QED

Resume bool_chain_compare_prefix_step[right_prefix]:
  `local_ptrs_reserved cenv s1` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z)` by
    metis_tac[not_fresh_at_mono] >>
  `return_buf_frame d cenv s1 t` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d cenv sa s` (irule_at Any) >>
     qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ mid _ _ t`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
      stmt_state_rel H ctx func cenv cx mid t /\ storage_well_formed_on cx mid (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!K. valid_horizon _ _ K mid.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> fs[expr_post_def]) >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type l) r mid (st0,s1,s2,shadow_s1,shadow_s2,y,t,G1,tn1)` by
    (simp[expr_sim_full_pre_def] >> metis_tac[expr_body_pre_gas_admissible]) >>
  qpat_assum `!mid t G1 tn1. _ ==> gas_prefix_full _ _ _ _ (mid,t,G1,tn1)`
    (drule_all_then assume_tac) >>
  qpat_assum `gas_prefix_full _ _ _ _ (mid,t,G1,tn1)`
    (mp_then Any irule (iffRL gas_prefix_full_state_cong)) >>
  qx_gen_tac `qe` >> Cases_on `bind (eval_expr cx r) (read_result cx) qe` >>
  rename1 `_ = (res,ee)` >> Cases_on `res` >> simp[bind_def]
QED

Finalise bool_chain_compare_prefix_step
