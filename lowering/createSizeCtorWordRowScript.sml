Theory createSizeCtorWordRow
Ancestors
  gasShadowCompileBase
  e2eDefs exprSimFullBundleProps gasExplicitSites gasSummary s1PrefixDefs venomExecSemantics
  vyperState relation list words pair bodyFullIfExpReach arithmetic exprLowering
  vfmConstants compileEnv exprLoweringProps exprBodyPreProps exprSimSource bodySimStmtFacts
  gasSummaryCompose bodyMemoryDefs rich_list exprSimHypsDefs vyperTypeSystem
  vyperTypeExprSoundness createCtorSavedSimple exprSimHyps bodyPtrDefs loweringPosts context
  fragGasPath vyperAST vyperStorageFootprint vyperTyping vyperValue integer_word
  abiEncodeArgsSim aggregateEvaluatedLayout loweringStateRelDefs ptrDiscipline bodySim
  createExprSizeExitDefs createSizePrefixReplay createSizeBlueprintKeywordReplay
  createSizeCtorValueRow

(* A word constructor completes at the snapshot cut, which includes its
   unwrap. Keep the full scalar post for the payload-length proof. *)
Theorem blueprint_ctor_word_row:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env e p /\ create_operand_completed_ok cx e /\
  is_word_type (lowered_value_type ce e) /\
  compile_expr ce (expr_type e) e a = (vv,m) /\
  compile_snapshot_vv ce copy (ext_call_arg_value (lowered_value_type ce e) vv) m = (sv,b) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha = (vv,shm) /\
  compile_snapshot_vv ce shcopy (ext_call_arg_value (lowered_value_type ce e) vv) shm = (sv,shb) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (a,b,sha,shb) /\
  local_ptrs_reserved ce a /\ (!K. dead_lo_ok K (DF K) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  return_buf_frame d ce a s /\ alloca_history fnc s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f i z. frag_reachable ctx fnc s f i z ==> dalloca_fmp_headroom i z) /\
  (!K. valid_horizon cx st0 K p.storage_trace ==>
    stmt_state_rel K ctx fnc ce cx p s /\ storage_well_formed_on cx p (FST K) /\
    ghost_inv_at (DF K) lo d ce cx p G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  create_expr_prefix a b (gas_explicit_sites ctx shctx) ctx fnc s chunk t /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  bind (eval_expr cx e) (read_result cx) p = (rr,q) /\
  valid_horizon cx st0 H q.storage_trace /\
  p.gas_obs = gas_explicit (chunk ++ rest) s.vs_gas_readings ++ tail ==>
  (?err. rr = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?v G' tn'. rr = INL v /\ q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail /\
    (!K op. valid_horizon cx st0 K q.storage_trace /\
      lower_value compile_expr ce (expr_type e) e a = (op,b) ==>
      expr_sim_full_post (DF,lo,d,ctx,fnc) ce cx e (p,a,b,s,op,G,tn)
        K (INL v : value + exception) (q with gas_obs := []) G' tn' t) /\
    expr_sim_inv ce cx env q /\
    (?tv ann. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
      evaluate_type (get_tenv cx) (expr_type e) = SOME ann /\
      arg_type_fits (lowered_value_type ce e) (expr_type e) /\
      value_has_type tv v /\ value_has_type ann v) /\
    return_buf_frame d ce b t /\ alloca_history fnc t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx fnc t f i z ==> dalloca_fmp_headroom i z) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!K. valid_horizon cx st0 K q.storage_trace ==>
      stmt_state_rel K ctx fnc ce cx q t /\ storage_well_formed_on cx q (FST K) /\
      ghost_inv_at (DF K) lo d ce cx q G' tn' t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ctor_snapshot_word_lower_value >> strip_tac >>
  drule expr_body_pre_lowered_fits >> strip_tac >>
  `is_word_type (expr_type e) /\ lowered_value_type ce e = expr_type e` by
    metis_tac[aggregateEvaluatedLayoutTheory.arg_type_fits_word_type,
              abiEncodeArgsSimTheory.abi_args_word_fits_eq] >>
  `lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha = (op,shb)` by
    (suspend "shadow") >>
  `gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
     tops cx st0 a b (bind (eval_expr cx e) (read_result cx)) (p,s,G,tn)
     (expr_sim_full_post (DF,lo,d,ctx,fnc) ce cx e (p,a,b,s,op,G,tn))` by
    (irule create_size_replay_value_cut >> simp[] >>
     conj_tac >- (qexists_tac `env` >> simp[]) >>
     qexistsl [`shfnc`, `sha`, `shb`, `expr_type e`] >>
     fs[expr_sim_full_pre_def, expr_sim_full_code_def] >>
     conj_tac >- (drule expr_body_pre_gas_admissible >> simp[]) >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!f i z. frag_reachable _ _ _ f i z ==> _` drule >> simp[]) >>
  `gas_path ctx fnc s (LENGTH chunk) (OK t)` by
    (qpat_assum `create_expr_prefix a b _ _ _ _ _ _`
       (mp_then Any mp_tac create_prefix_gas_path) >> simp[]) >>
  `p.gas_obs = gas_explicit chunk s.vs_gas_readings ++
               (gas_explicit rest t.vs_gas_readings ++ tail)` by
    (drule gas_explicit_append_path >> simp[APPEND_ASSOC]) >>
  drule_all blueprint_ctor_complete >> strip_tac
  >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
  disj2_tac >> suspend "finish"
QED

Resume blueprint_ctor_word_row[shadow]:
  `reason_uniform_shape compile_expr ce (expr_type e) e` by
    (irule exprReasonOperandTheory.compile_expr_reason_uniform >> qexists_tac `env` >>
     drule expr_body_pre_static_facts >> simp[expr_sim_inv_def]) >>
  `vv_type vv = expr_type e` by
    (fs[exprReasonOperandTheory.reason_uniform_shape_def] >> first_x_assum drule >>
     Cases_on `vv` >> gvs[exprReasonOperandTheory.reason_result_shape_def, vv_type_def]) >>
  `ext_call_arg_value (lowered_value_type ce e) vv = vv` by
    (Cases_on `vv` >> gvs[ext_call_arg_value_def, vv_type_def]) >>
  Cases_on `unwrap_value ce vv shm` >>
  gvs[lower_value_def, compile_snapshot_vv_def, comp_bind_def, comp_return_def]
QED

Resume blueprint_ctor_word_row[finish]:
  pop_assum (mk_asm "replay") >>
  asm "replay" (qspec_then `H` mp_tac) >> (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [expr_sim_full_post_def, expr_sim_full_endpoint_def, expr_post_def])) >>
  qexistsl_tac [`v`,`G'`,`tn'`] >> simp[] >>
  `expr_sim_inv ce cx env q /\ value_runtime_typed env (expr_type e) v` by
    (drule_all (REWRITE_RULE [ETA_AX] bodySimStmtFactsTheory.expr_body_pre_eval) >> simp[]) >>
  `env.type_defs = get_tenv cx` by metis_tac[expr_body_pre_env_type_defs] >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v` by
    fs[value_runtime_typed_def] >>
  `a.cs_next_var <= b.cs_next_var` by
    (qspecl_then [`ce`,`expr_type e`,`e`,`a`] mp_tac ci_mono_lower_value_compile_expr >>
     simp[ci_mono_def]) >>
  `return_buf_frame d ce b t` by
    (irule return_buf_frame_frame >> qexistsl [`ce`,`s`,`a`] >> simp[]) >>
  `MEM fnc ctx.ctx_functions` by fs[expr_sim_full_code_def] >>
  `!bb. MEM bb fnc.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0`
    by metis_tac[body_inv_no_phi] >>
  `!f i z. frag_reachable ctx fnc t f i z ==> dalloca_fmp_headroom i z` by
    (drule gas_origin_ptr_path_dalloca_fmp_headroom >> simp[] >> metis_tac[]) >>
  `~t.vs_halted` by (drule gas_path_normal >> simp[]) >>
  simp[] >> conj_tac
  >- (qx_gen_tac `hor` >> strip_tac >> asm "replay" (qspec_then `hor` mp_tac) >>
      (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
      qpat_assum `rr = INL v` (fn th => disch_then (ACCEPT_TAC o REWRITE_RULE [th] o CONJUNCT2))) >>
  conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
  qx_gen_tac `hor` >> disch_tac >>
  asm "replay" (qspec_then `hor` mp_tac) >> (impl_tac >- FIRST_ASSUM ACCEPT_TAC) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [expr_sim_full_post_def, expr_post_def]) >>
  conj_tac >- FIRST_ASSUM ACCEPT_TAC >> conj_tac
  >- (irule (iffLR storage_well_formed_on_backends) >>
      qexists_tac `q with gas_obs := []` >> simp[]) >>
  qpat_assum `ghost_inv_at (DF hor) _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [ghost_inv_at_def]) >>
  simp[ghost_inv_at_def] >> FIRST_ASSUM ACCEPT_TAC
QED

Finalise blueprint_ctor_word_row
