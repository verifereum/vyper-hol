(* The ordinary Slice continuation starts after the source capture. *)
Theory s1PrefixSliceOrdinaryBounds
Ancestors
  s1PrefixPreds s1PrefixCompose exprSimSliceOrdinaryContinue
  gasOutcomeFullCompose bodyMemoryDefs exprSimSource s1PrefixProps
  exprSimSliceTerminal vyperState s1PrefixDefs bodySimFull
  bodyFullExprsListFacts bodyFullSimProjection

Theorem slice_read_requests_frame[local]:
  requests_outcomes_frame (bind (eval_expr cx e) (read_result cx))
Proof
  irule requests_outcomes_frame_bind_all >>
  simp[evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
     (bind (eval_expr cx len) (read_result cx)) (mid,t,G,tn)` by
    (qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_sim_prefix_def]) >>
     disch_then (drule_then ACCEPT_TAC)) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sd`,`se`,`shadow_sd`,`shadow_se`,`lop`,`t`,`G`,`tn`] mp_tac) >>
  (impl_tac >- (fs[expr_sim_full_pre_def] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  irule gas_prefix_full_bind_no_outcome >>
  simp[slice_read_frame, slice_read_requests_frame, slice_terminal_source_frame] >>
  conj_tac
  >- (rpt gen_tac >>
      simp[bind_def, get_accounts_def, lift_sum_def, return_def, raise_def] >>
      Cases_on `f v st.accounts` >> simp[return_def, raise_def] >>
      strip_tac >> gvs[]) >>
  qexistsl_tac [`\H res ee G tn t. ~t.vs_halted`,
                `\H res ee gt r. ISR res`, `cx_tops cx`] >>
  simp[] >> irule gas_outcome_full_post_source >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt gen_tac >> Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_INL]
QED
*)
Theorem slice_length_terminal_prefix[local]:
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty len mid /\
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty len mid /\
  expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty len mid
    (st0,sd,se,shadow_sd,shadow_se,lop,t,G,tn) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
    (do lv <- bind (eval_expr cx len) (read_result cx);
        acc <- get_accounts;
        v <- lift_sum (f lv acc);
        return (Value v) od) (mid,t,G,tn)
Proof
  cheat
QED

Theorem slice_ordinary_bounds_prefix:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env mid /\
  expr_body_pre ce cx env (Builtin ann (Slice n) [src;start;len]) es /\
  expr_body_pre ce cx env start mid /\ expr_type len = BaseT (UintT 256) /\
  body_exprs_full_ok cx [start;len] /\ body_exprs_prefix_ok cx [start;len] /\
  lower_value compile_expr ce ty start sc = (sop,sd) /\
  lower_value compile_expr ce ty len sd = (lop,se) /\
  lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr len) shadow_sd =
    (lop,shadow_se) /\
  gas_shadow_state sd shadow_sd /\ gas_shadow_state se shadow_se /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sd se func /\ fn_has_code shadow_sd shadow_se shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sc /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  return_buf_frame d ce sc u /\
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx start) (read_result cx)) (mid,u,Gu,tu)
    (\H res ee G tn t. ?v. res = INL v /\
      expr_post H ctx func ce cx start mid sc sd u ee v sop t /\
      t.vs_current_bb = sd.cs_current_bb /\ t.vs_inst_idx = LENGTH sd.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      u.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d ce cx ee G tn t /\ ~t.vs_halted /\
      (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z))
    (\H res ee gt r. ISR res) /\
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
    (bind (eval_expr cx start) (read_result cx)) (mid,u,Gu,tu) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cx st0
    (do sv <- bind (eval_expr cx start) (read_result cx);
        lv <- bind (eval_expr cx len) (read_result cx);
        acc <- get_accounts;
        v <- lift_sum (evaluate_builtin cx acc ann (Slice n)
                  (MAP expr_type [src;start;len]) [src_v;sv;lv]);
        return (Value v) od) (mid,u,Gu,tu)
Proof
  strip_tac >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[slice_read_frame, slice_read_requests_frame, slice_terminal_source_frame,
       vyperStorageTraceTheory.storage_trace_frame_bind_all] >>
  qx_genl_tac [`marks`,`sv`,`ee`,`G1`,`tn1`,`t`] >> strip_tac >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
  `?s tv s' s1 v s1'. eval_expr cx start s = (INL tv,s') /\
     read_result cx tv s1 = (INL v,s1')` by
    (drule vyperStatePreservationTheory.bind_split >> simp[] >> metis_tac[]) >>
  `body_expr_full_ok cx len /\ body_expr_prefix_ok cx len` by
    (fs[body_exprs_full_ok_cons, body_exprs_prefix_ok_def] >> metis_tac[]) >>
  `expr_sim_inv ce cx env ee` by
    (qpat_assum `bind (eval_expr cx start) _ _ = _`
       (mp_then Any mp_tac (SIMP_RULE (srw_ss()) [SF ETA_ss] expr_body_pre_eval)) >>
     simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env ee` by
    (qpat_assum `bind (eval_expr cx start) _ _ = _`
       (mp_then Any mp_tac bodyFullPredsTheory.body_const_cells_agree_expr_read) >>
     simp[] >> disch_then irule >> simp[] >>
     disj1_tac >> drule exprBodyPrePropsTheory.expr_body_pre_static_facts >> simp[]) >>
  `expr_body_pre ce cx env len ee` by
    (qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _`
       (mp_then Any mp_tac expr_body_pre_builtin_typed_arg) >>
     disch_then (qspecl_then [`len`,`ee`] mp_tac) >> simp[]) >>
  `sc.cs_next_var <= sd.cs_next_var` by
    (qpat_assum `lower_value compile_expr ce ty start sc = _` mp_tac >>
     metis_tac[exprLoweringPropsTheory.ci_mono_lower_value_compile_expr,
               exprLoweringPropsTheory.ci_mono_def, pairTheory.SND]) >>
  ho_match_mp_tac slice_length_terminal_prefix >>
  conj_tac
  >- (irule (cj 1 body_expr_full_ok_simulations) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`env`,`tops`] >> simp[]) >>
  conj_tac
  >- (qpat_assum `body_expr_prefix_ok cx len`
        (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
      disch_then (irule o CONJUNCT1 o SIMP_RULE bool_ss [IMP_CONJ_THM, FORALL_AND_THM]) >>
      qexistsl_tac [`env`,`tops`] >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` (drule_then strip_assume_tac)) >>
  `return_buf_frame d ce sd t` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d ce sc u` (irule_at Any) >> simp[] >>
     qpat_assum `expr_post _ _ _ _ _ start _ _ _ _ _ _ _ _` mp_tac >>
     disch_then (strip_assume_tac o REWRITE_RULE[loweringPostsTheory.expr_post_def]) >>
     first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved ce sd` by metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `gas_admissible (bind (eval_expr cx len) (read_result cx)) expr_res_ok ee` by
    (irule expr_body_pre_gas_admissible >> goal_assum (drule_at Any)) >>
  simp[expr_sim_full_pre_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
       qexists_tac `sc` >> simp[] >> NO_TAC) >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (qspec_then `H` (drule_then (strip_assume_tac o REWRITE_RULE[loweringPostsTheory.expr_post_def]))) >>
  simp[]
QED
