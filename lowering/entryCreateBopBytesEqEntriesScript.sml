(* The right comparison operand starts at the completed left operand's
   actual source and machine states, with its selected ghosts. *)
Theory entryCreateBopBytesEqEntries
Ancestors
  s1PrefixDefs exprSimFullBundleProps bodyFullIfExpReach bodyFullPreds
  exprSimSource exprSimHyps exprBodyPreProps exprLoweringProps
  loweringShapeDefs bodyMemoryDefs loweringPosts fragGasOriginPtrExec fragExec
  vyperTypeSystem vyperState

Theorem create_bop_bytes_eq_operand_entries:
  body_inv tops ctx ce cx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  (bop = Eq \/ bop = NotEq) /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
    (Builtin ann (Bop bop) [e1;e2]) es (st0,sa,sb,sha,shb,op,s0,G0,tn0) /\
  lower_value compile_expr ce (expr_type e1) e1 sa = (x,s1) /\
  lower_value compile_expr ce (expr_type e1) e2 s1 = (y,s2) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type e1)
    (gas_shadow_expr e1) sha = (x,sh1) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type e1)
    (gas_shadow_expr e2) sh1 = (y,sh2) /\
  gas_shadow_state s1 sh1 /\ gas_shadow_state s2 sh2 /\
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
  fn_has_code sha sh1 shfunc /\ fn_has_code sh1 sh2 shfunc /\
  sa.cs_next_var <= s1.cs_next_var ==>
  expr_type e2 = expr_type e1 /\ ann = BaseT BoolT /\
  expr_body_pre ce cx env e1 es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx (expr_type e1)
    e1 es (st0,sa,s1,sha,sh1,x,s0,G0,tn0) /\
  (!incoming outgoing v1 mid t G1 tn1 left H0.
    bind (eval_expr cx e1) (read_result cx) (es with gas_obs := incoming) =
      (INL v1,mid with gas_obs := outgoing) /\ mid.gas_obs = [] /\
    valid_horizon cx st0 H0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
        (s0,G0,tn0) left (OK t,G1,tn1) /\
      expr_sim_full_post (DF,lo,d,ctx,func) ce cx e1
        (es,sa,s1,s0,x,G0,tn0) H (INL v1) mid G1 tn1 t) ==>
    (?tv et. eval_expr cx e1 (es with gas_obs := incoming) = (INL tv,et) /\
             read_result cx tv et = (INL v1,mid with gas_obs := outgoing)) /\
    expr_sim_inv ce cx env mid /\ expr_body_pre ce cx env e2 mid /\
    body_const_cells_agree [(NONE,tops)] cx env mid /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx (expr_type e1)
      e2 mid (st0,s1,s2,sh1,sh2,y,t,G1,tn1))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule expr_body_pre_bop >> strip_tac >>
  `expr_type e2 = expr_type e1 /\ ann = BaseT BoolT` by
    (qpat_assum `bop = Eq \/ bop = NotEq` strip_assume_tac >>
     gvs[well_typed_binop_def]) >>
  qpat_x_assum `expr_sim_full_pre _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[expr_sim_full_pre_def]) >>
  simp[] >> conj_tac
  >- (simp[expr_sim_full_pre_def] >> conj_tac
      >- (irule expr_body_pre_gas_admissible >> first_assum (irule_at Any)) >>
      first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre ce cx env e1 (es with gas_obs := incoming)` by
    simp[expr_body_pre_gas_obs] >>
  conj_tac >- metis_tac[REWRITE_RULE[ETA_AX] eval_expr_read_INL] >>
  `expr_sim_inv ce cx env mid` by
    (drule_all (REWRITE_RULE[ETA_AX] exprSimSourceTheory.expr_body_pre_eval) >> simp[]) >>
  `expr_body_pre ce cx env e2 mid` by metis_tac[] >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`body_const_cells_agree [(NONE,tops)] cx env (mid with gas_obs := outgoing)`
       suffices_by simp[] >>
     irule body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx e1) _ _ = _` (irule_at Any) >>
     simp[] >> metis_tac[expr_body_pre_static_facts]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o SIMP_RULE bool_ss
    [expr_sim_full_post_def,expr_sim_full_endpoint_def,sumTheory.INL_11]) >>
  `~t.vs_halted` by
    (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  `!fn i u. frag_reachable ctx func t fn i u ==> dalloca_fmp_headroom i u` by
    (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0`
       by metis_tac[body_inv_no_phi] >>
     metis_tac[gas_origin_ptr_path_dalloca_fmp_headroom]) >>
  `return_buf_frame d ce s1 t` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame d ce sa s0` (irule_at Any) >>
     fs[expr_post_def]) >>
  `gas_admissible (bind (eval_expr cx e2) (read_result cx)) expr_res_ok mid` by
    (irule expr_body_pre_gas_admissible >> first_assum (irule_at Any)) >>
  `local_ptrs_reserved ce s1` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z) /\
   (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z)` by
    metis_tac[not_fresh_at_mono] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func ce cx mid t /\
       storage_well_formed_on cx mid (FST H) /\
       ghost_inv_at (DF H) lo d ce cx mid G1 tn1 t` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp_tac bool_ss [expr_sim_full_post_def,sumTheory.INL_11,expr_post_def] >>
     strip_tac >> simp[]) >>
  rewrite_tac[expr_sim_full_pre_def] >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
QED
