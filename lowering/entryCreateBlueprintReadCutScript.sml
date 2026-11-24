Theory entryCreateBlueprintReadCut
Ancestors
  e2eDefs exprSimFullBundleProps fragGasOrigin gasExplicitSites gasSummary s1PrefixDefs
  venomExecSemantics venomState vyperState relation list words createMarkedPath
  pair bodyFullIfExpReach arithmetic exprLowering vfmConstants compileEnv exprLoweringProps
  exprBodyPreProps exprSimSource bodySimStmtFacts vyperStorageTrace gasSummaryCompose
  bodyMemoryDefs exprOperandVar freshWrites rich_list exprSimHypsDefs
  accountsRelProps bodyPtrDefs loweringPosts fragGasPath vyperAST vyperStorageFootprint
  vyperTyping vyperValue integer_word valueEncoding loweringStateRelDefs ptrDiscipline
  bodySim loweringShapeDefs createExprSizeExitDefs createSizePrefixReplay

(* Only the replay of this invocation, with its actual full pre, is needed. *)
Theorem blueprint_read_at_cut_from_replay:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env e p /\
  (expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fnc,shfnc) ce cx (expr_type e) e p
     (st0,ca,cb,sca,scb,op,u,G,tn) ==>
   gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
     tops cx st0 ca cb (bind (eval_expr cx e) (read_result cx)) (p,u,G,tn)
     (expr_sim_full_post (DF,lo,d,ctx,fnc) ce cx e (p,ca,cb,u,op,G,tn))) /\
  lower_value compile_expr ce (expr_type e) e ca = (op,cb) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sca = (op,scb) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cb,sca,scb) /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca u /\ alloca_history fnc u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p u /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at (DF h) lo d ce cx p G tn u) /\
  ~u.vs_halted /\ u.vs_current_bb = ca.cs_current_bb /\
  u.vs_inst_idx = LENGTH ca.cs_current_insts /\
  create_expr_prefix ca cb (gas_explicit_sites ctx shctx) ctx fnc u chunk t /\
  t.vs_current_bb = cb.cs_current_bb /\ t.vs_inst_idx = LENGTH cb.cs_current_insts /\
  (!v. storage_trace_frame (k v)) /\
  bind (bind (eval_expr cx e) (read_result cx)) k p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (chunk ++ rest) u.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?v q G' tn'.
    bind (eval_expr cx e) (read_result cx) p = (INL v,q) /\ k v q = (res,out) /\
    q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail /\
    valid_horizon cx st0 H q.storage_trace /\
    expr_sim_inv ce cx env q /\ value_runtime_typed env (expr_type e) v /\
    expr_val_rel cx (post_value_type ce e) v op t /\
    ca.cs_next_var <= cb.cs_next_var /\
    (!x w. not_fresh_at ca x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w) /\
    return_buf_frame d ce cb t /\ alloca_history fnc t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx fnc t f i z ==> dalloca_fmp_headroom i z) /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx fnc ce cx q t /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at (DF h) lo d ce cx q G' tn' t) /\ ~t.vs_halted
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fnc,shfnc) ce cx (expr_type e) e p
     (st0,ca,cb,sca,scb,op,u,G,tn)` by
    (fs[expr_sim_full_pre_def, expr_sim_full_code_def] >>
     conj_tac >- (drule expr_body_pre_gas_admissible >> simp[]) >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!f i z. frag_reachable _ _ _ f i z ==> _` drule >> simp[]) >>
  qpat_x_assum `expr_sim_full_pre _ _ _ _ _ _ _ ==> _` (drule_then assume_tac) >>
  `gas_path ctx fnc u (LENGTH chunk) (OK t)` by
    (qpat_assum `create_expr_prefix ca cb _ _ _ _ _ _`
       (mp_then Any mp_tac create_prefix_gas_path) >> simp[]) >>
  `p.gas_obs = gas_explicit chunk u.vs_gas_readings ++
               (gas_explicit rest t.vs_gas_readings ++ tail)` by
    (drule gas_explicit_append_path >> simp[APPEND_ASSOC]) >>
  Cases_on `bind (eval_expr cx e) (read_result cx) p` >>
  qmatch_asmsub_rename_tac `bind (eval_expr cx e) (read_result cx) p = (rr,mid)` >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (Cases_on `rr` >> fs[bind_def] >> metis_tac[vyperStorageFootprintTheory.valid_horizon_frame]) >>
  `p with gas_obs := gas_explicit chunk u.vs_gas_readings ++
                       (gas_explicit rest t.vs_gas_readings ++ tail) = p`
    by (qpat_assum `p.gas_obs = gas_explicit chunk _ ++ _`
          (once_rewrite_tac o single o SYM) >> simp[]) >>
  qhdtm_x_assum `gas_completed_operand` mp_tac >>
  simp[gas_completed_operand_def] >>
  disch_then (qspecl_then [`H`,`chunk`,`t`,
    `gas_explicit rest t.vs_gas_readings ++ tail`,`rr`,`mid`] mp_tac) >>
  simp[] >> strip_tac
  >- (disj2_tac >>
      `?v. rr = INL v` by
        (qpat_assum `!h. valid_horizon _ _ h mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
           (qspec_then `H` mp_tac) >>
         (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
         rewrite_tac[expr_sim_full_post_def] >> simp[] >> strip_tac >> metis_tac[]) >>
      gvs[] >> rename1 `_ = (INL v,mid)` >>
      `k v mid = (res,out)` by fs[bind_def] >>
      drule_all (REWRITE_RULE[ETA_AX] bodySimStmtFactsTheory.expr_body_pre_eval) >>
      simp[] >> strip_tac >>
      qexistsl [`G'`, `tn'`] >> simp[] >>
      `ci_mono ca cb` by
        (qspecl_then [`ce`, `expr_type e`, `e`, `ca`] mp_tac
           ci_mono_lower_value_compile_expr >> simp[]) >>
      `ca.cs_next_var <= cb.cs_next_var` by fs[ci_mono_def] >>
      `!h. valid_horizon cx st0 h mid.storage_trace ==>
        gas_origin_ptr_path (DF h,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
          (u,G,tn) chunk (OK t,G',tn') /\
        expr_post h ctx fnc ce cx e p ca cb u (mid with gas_obs := []) v op t /\
        expr_sim_full_endpoint fnc cb u t /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        ghost_inv_at (DF h) lo d ce cx (mid with gas_obs := []) G' tn' t` by
        (qx_gen_tac `h` >> disch_tac >>
         qpat_assum `!h. valid_horizon _ _ h mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
           (qspec_then `h` mp_tac) >> (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
         disch_then (CONJUNCTS_THEN2 assume_tac
           (strip_assume_tac o SIMP_RULE (srw_ss()) [expr_sim_full_post_def])) >> simp[]) >>
      qpat_assum `!h. valid_horizon _ _ h mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (qspec_then `H` mp_tac) >> (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
      disch_then (strip_assume_tac o SIMP_RULE (srw_ss())
        [expr_post_def, expr_sim_full_endpoint_def]) >>
      `return_buf_frame d ce cb t` by
        (irule return_buf_frame_frame >> qexistsl [`ce`,`u`,`ca`] >> simp[]) >>
      `MEM fnc ctx.ctx_functions` by fs[expr_sim_full_code_def] >>
      `!bb. MEM bb fnc.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0`
        by metis_tac[body_inv_no_phi] >>
      `!f i z. frag_reachable ctx fnc t f i z ==> dalloca_fmp_headroom i z` by
        (drule gas_origin_ptr_path_dalloca_fmp_headroom >> simp[] >> metis_tac[]) >>
      simp[] >> (conj_tac >- FIRST_ASSUM ACCEPT_TAC) >> conj_tac
      >- (qx_gen_tac `h` >> disch_tac >>
          qpat_assum `!h. valid_horizon _ _ h mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
            (qspec_then `h` mp_tac) >> (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
          disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [expr_post_def]) >>
          conj_tac >- FIRST_ASSUM ACCEPT_TAC >> conj_tac
          >- (irule (iffLR storage_well_formed_on_backends) >>
              qexists_tac `mid with gas_obs := []` >> simp[]) >>
          qpat_assum `ghost_inv_at (DF h) _ _ _ _ _ _ _ _`
            (strip_assume_tac o SIMP_RULE (srw_ss()) [ghost_inv_at_def]) >>
          simp[ghost_inv_at_def] >> FIRST_ASSUM ACCEPT_TAC) >>
      drule gas_path_normal >> simp[]) >>
  fs[bind_def] >> metis_tac[]
QED
