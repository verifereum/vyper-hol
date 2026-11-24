(* Entry to the second word operand, at the selected return of the first. *)
Theory entryCreateBopWordRightEntry
Ancestors
  s1PrefixDefs exprSimFullBundleProps bodyFullIfExpReach bodyFullPreds
  exprBodyPreProps exprSimSource exprSimHyps exprLoweringProps freshWrites
  bodyMemoryDefs loweringPosts fragGasOriginPtrExec vyperStorageTrace
  vyperStorageFootprint fragExec

Theorem bop_word_right_source[local]:
  expr_body_pre ce cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  mid.gas_obs = [] /\
  vyperState$bind (eval_expr cx e1) (read_result cx) (es with gas_obs := incoming) =
    (INL v1, mid with gas_obs := outgoing) ==>
  (?s tv u s' v u'. eval_expr cx e1 s = (INL tv,u) /\
                     read_result cx tv s' = (INL v,u')) /\
  expr_body_pre ce cx env e2 mid /\
  body_const_cells_agree [(NONE,tops)] cx env mid
Proof
  strip_tac >> drule expr_body_pre_bop >> strip_tac >>
  `expr_body_pre ce cx env e1 (es with gas_obs := incoming)` by simp[] >>
  `body_const_cells_agree [(NONE,tops)] cx env (es with gas_obs := incoming)` by simp[] >>
  drule_then strip_assume_tac (REWRITE_RULE[ETA_THM] eval_expr_read_INL) >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (`expr_sim_inv ce cx env (mid with gas_obs := outgoing)` suffices_by simp[] >>
      drule_all (REWRITE_RULE[ETA_THM] exprSimSourceTheory.expr_body_pre_eval) >> simp[]) >>
  `well_typed_expr env e1` by (drule expr_body_pre_static_facts >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env (mid with gas_obs := outgoing)`
    suffices_by simp[] >>
  irule body_const_cells_agree_expr_read >>
  goal_assum (drule_at (Pat `vyperState$bind (eval_expr _ _) _ _ = _`)) >> simp[]
QED

Theorem create_bop_word_right_entry:
  body_inv tops ctx ce cx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
    (Builtin ann (Bop bop) [e1;e2]) es (st0,sa,sb,sha,shb,op,s0,G0,tn0) /\
  lower_value compile_expr ce (expr_type e1) e2 s1 = (y,s2) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type e1) (gas_shadow_expr e2) sh1 =
    (y,sh2) /\
  gas_shadow_state s1 sh1 /\ gas_shadow_state s2 sh2 /\
  fn_has_code s1 s2 func /\ fn_has_code sh1 sh2 shfunc /\
  sa.cs_next_var <= s1.cs_next_var /\ mid.gas_obs = [] /\
  (?incoming outgoing.
     vyperState$bind (eval_expr cx e1) (read_result cx) (es with gas_obs := incoming) =
       (INL v1, mid with gas_obs := outgoing)) /\
  valid_horizon cx st0 H0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     expr_sim_full_post (DF,lo,d,ctx,func) ce cx e1 (es,sa,s1,s0,x,G0,tn0)
       H (INL v1) mid G1 tn1 t /\
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
       (s0,G0,tn0) marks (OK t,G1,tn1)) ==>
  (?s tv u s' v u'. eval_expr cx e1 s = (INL tv,u) /\
                     read_result cx tv s' = (INL v,u')) /\
  expr_body_pre ce cx env e2 mid /\
  body_const_cells_agree [(NONE,tops)] cx env mid /\
  valid_horizon cx st0 H0 es.storage_trace /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx (expr_type e1) e2 mid
    (st0,s1,s2,sh1,sh2,y,t,G1,tn1)
Proof
  strip_tac >> drule_all bop_word_right_source >> strip_tac >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (`valid_horizon cx st0 H0 (es with gas_obs := incoming).storage_trace`
        suffices_by simp[] >>
      `storage_trace_frame (vyperState$bind (eval_expr cx e1) (read_result cx))` by
        simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
             storage_trace_frame_read_result] >>
      `valid_horizon cx st0 H0 (mid with gas_obs := outgoing).storage_trace` by simp[] >>
      drule_all valid_horizon_frame >> simp[]) >>
  fs[expr_sim_full_pre_def] >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (drule body_inv_no_phi >> disch_then drule >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H0` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `!fn i u. frag_reachable ctx func t fn i u ==> dalloca_fmp_headroom i u` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t,G1,tn1)`
       (mp_then (Pos hd) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     asm_rewrite_tac[]) >>
  `~t.vs_halted` by
    (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  `local_ptrs_reserved ce s1` by metis_tac[local_ptrs_reserved_next_var] >>
  `gas_admissible (vyperState$bind (eval_expr cx e2) (read_result cx)) expr_res_ok mid` by
    (drule expr_body_pre_gas_admissible >> simp[]) >>
  qpat_assum `expr_sim_full_post _ _ _ e1 _ H0 _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss
       [expr_sim_full_post_def,expr_sim_full_endpoint_def]) >>
  `return_buf_frame d ce s1 t` by
    (irule return_buf_frame_frame >> qpat_assum `return_buf_frame d ce sa s0` (irule_at Any) >>
     fs[expr_post_def]) >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[])
  >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[])
  >- (qpat_assum `!fn i u. frag_reachable ctx func t fn i u ==> _` ACCEPT_TAC) >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o SIMP_RULE bool_ss [expr_sim_full_post_def,expr_post_def]) >>
  simp[]
QED
