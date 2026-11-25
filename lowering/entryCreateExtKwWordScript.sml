Theory entryCreateExtKwWord
Ancestors
  entryCreateFocusSpec gasShadowCompile gasShadowCompileHelpers
  gasOriginPtrLabels fragGasOriginPtrExec exprOperandVar exprLoweringProps
  exprSimSource exprSimWordArgs exprSimSend stmtSimDefs
  gasShadowState exprLowering compileEnv vyperTypeSystem vyperTyping vyperState
  s1PrefixDefs exprSimFullBundleProps loweringPosts bodyPtrDefs
  fragExec entryCreateCompletedCut vyperValue

(* For the word branches the compiler's final comp_return only changes the
   result pair: its operand interval is exactly the lower_value interval. *)
Theorem extcall_kw_word_layout[local]:
  ~(k = EKDefault /\ ~is_word_type rt) /\
  compile_ext_call_kwarg compile_expr ce rt k e sa = ((op,dt),sb) /\
  compile_ext_call_kwarg compile_expr (gas_shadow_env T ce) rt k
    (gas_shadow_expr e) sha = (shadow_result,shb) /\
  gas_shadow_state sa sha ==>
  dt = rt /\ gas_shadow_state sb shb /\
  lower_value compile_expr ce (ext_call_kw_type rt k) e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T ce) (ext_call_kw_type rt k)
    (gas_shadow_expr e) sha = (op,shb)
Proof
  strip_tac >>
  `gas_shadow_compiles (compile_ext_call_kwarg compile_expr ce rt k e)
     (compile_ext_call_kwarg compile_expr (gas_shadow_env T ce) rt k (gas_shadow_expr e))` by
    (irule (SIMP_RULE bool_ss []
       (Q.INST [`sh` |-> `T`] gas_shadow_compiles_ext_call_kwarg_env)) >>
     simp[cj 1 gas_shadow_compile_expr_env]) >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  disch_then (qspecl_then [`sa`,`sha`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `compile_ext_call_kwarg _ _ _ _ e _ = _` mp_tac >>
  qpat_x_assum `compile_ext_call_kwarg _ _ _ _ (gas_shadow_expr e) _ = _` mp_tac >>
  simp[compile_ext_call_kwarg_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  Cases_on `k` >> gvs[ext_call_kw_type_def] >> rpt strip_tac >> gvs[]
QED

Definition extcall_kw_word_post_def:
  extcall_kw_word_post (DF,lo,d,ctx,func) ce cx rt k (es,sa,sb,s0,op,G0,tn0)
      H res ee G tn t <=>
    ?v. res = INL v /\
      stmt_state_rel H ctx func ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ~t.vs_halted /\ alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at (DF H) lo d ce cx ee G tn t /\
      ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
      return_buf_frame d ce sb t /\ wb_frame ce es ee sa s0 t /\
      MAP FDOM ee.scopes = MAP FDOM es.scopes /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      t.vs_labels = s0.vs_labels /\ (!x. op = Var x ==> not_fresh_at sb x) /\
      (k <> EKDefault ==> ?w. eval_operand op t = SOME w /\
        dest_NumV v = SOME (w2n w) /\ op_taint tn op = {}) /\
      (k = EKDefault ==> expr_val_rel cx rt v op t /\ ptr_val_ok cx rt v op G tn t)
End

Theorem extcall_kw_word_post_intro[local]:
  ~(k = EKDefault /\ ~is_word_type rt) /\ expr_type e = ext_call_kw_type rt k /\
  expr_body_pre ce cx env e es /\ return_buf_frame d ce sa s0 /\ local_ptrs_reserved ce sa /\
  lower_value compile_expr ce (ext_call_kw_type rt k) e sa = (op,sb) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) = (res,ee) /\
  expr_sim_full_post (DF,lo,d,ctx,func) ce cx e (es,sa,sb,s0,op,G0,tn0) H res ee G tn t /\
  gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (s0,G0,tn0) marks (OK t,G,tn) ==>
  extcall_kw_word_post (DF,lo,d,ctx,func) ce cx rt k (es,sa,sb,s0,op,G0,tn0) H res ee G tn t
Proof
  strip_tac >> gvs[expr_sim_full_post_def, expr_sim_full_endpoint_def] >>
  `is_word_type (expr_type e)` by
    (Cases_on `k` >> gvs[ext_call_kw_type_def,is_word_type_def]) >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (drule eval_read_preserves_scopes_dom >> simp[]) >>
  `t.vs_labels = s0.vs_labels` by (drule_then ACCEPT_TAC gas_origin_ptr_path_preserves_labels) >>
  `~t.vs_halted` by (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  `wb_frame ce es ee sa s0 t` by (drule exprSimWordArgsTheory.expr_post_frame >> simp[]) >>
  `!x. op = Var x ==> not_fresh_at sb x` by
    (drule compiler_lower_value_var >> metis_tac[cj 1 compiler_compile_var]) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (qspecl_then [`ce`,`ext_call_kw_type rt k`,`e`,`sa`] mp_tac ci_mono_lower_value_compile_expr >>
     simp[ci_mono_def]) >>
  `return_buf_frame d ce sb t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`ce`,`s0`,`sa`] >> fs[expr_post_def]) >>
  fs[extcall_kw_word_post_def, expr_post_def] >> conj_tac
  >- (strip_tac >> `expr_type e = BaseT (UintT 256)` by
        (Cases_on `k` >> gvs[ext_call_kw_type_def]) >>
      `expr_body_pre ce cx env e (es with gas_obs := obs)` by simp[] >>
      drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_word_value) >>
      simp[evaluate_type_def] >> strip_tac >>
      fs[expr_val_rel_def, ptr_val_ok_def, is_word_type_def, evaluate_type_def, uint256_typed_dest]) >>
  strip_tac >> gvs[ext_call_kw_type_def]
QED

Theorem extcall_kw_word_scoped_cut:
  ~(k = EKDefault /\ ~is_word_type rt) /\ expr_type e = ext_call_kw_type rt k /\
  compile_ext_call_kwarg compile_expr ce rt k e sa = ((op,dt),sb) /\
  compile_ext_call_kwarg compile_expr (gas_shadow_env T ce) rt k
    (gas_shadow_expr e) sha = (shadow_result,shb) /\
  gas_shadow_state sa sha /\ gas_shadow_context ctx shctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shfunc /\ MEM func ctx.ctx_functions /\ MEM shfunc shctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code sha shb shfunc /\ fn_inst_ids_distinct func /\
  expr_body_pre ce cx env e es /\ local_ptrs_reserved ce sa /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ create_operand_at sa s0 /\
  expr_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx (ext_call_kw_type rt k) e es /\
  (expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx (ext_call_kw_type rt k) e es
    (st0,sa,sb,sha,shb,op,s0,G0,tn0) ==>
    create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
      (bind (eval_expr cx e) (read_result cx)) (es,s0)) ==>
  dt = rt /\
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
    (cx_tops cx) cx st0 sa sb (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (extcall_kw_word_post (DF,lo,d,ctx,func) ce cx rt k (es,sa,sb,s0,op,G0,tn0))
    (create_operand_exit_post ctx cx) /\
  create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0)
Proof
  strip_tac >> drule_all extcall_kw_word_layout >> strip_tac >> simp[] >>
  drule expr_body_pre_gas_admissible >> strip_tac >>
  `expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx (ext_call_kw_type rt k) e es
    (st0,sa,sb,sha,shb,op,s0,G0,tn0)` by
    (pure_rewrite_tac[expr_sim_full_pre_def] >> rpt conj_tac >>
     (FIRST_ASSUM ACCEPT_TAC ORELSE fs[create_operand_at_def])) >>
  reverse conj_tac >- (first_x_assum drule >> simp[]) >>
  qpat_x_assum `expr_sim_scoped _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_scoped_def]) >>
  disch_then (drule_then mp_tac) >>
  simp_tac bool_ss [scoped_operand_outcome_def] >>
  disch_then (qx_choose_then `marks` assume_tac) >> qexists_tac `marks` >>
  pop_assum (DISJ_CASES_THEN2 assume_tac (DISJ_CASES_THEN2 strip_assume_tac assume_tac))
  >- simp[]
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
      disj1_tac >> irule extcall_kw_word_post_intro >> simp[] >>
      conj_tac >- (qexistsl_tac [`gas_explicit_sites ctx shctx`,`PG`,`marks`] >> simp[]) >>
      qexistsl_tac [`e`,`env`,`gas_explicit marks s0.vs_gas_readings`] >> simp[] >>
      qpat_assum `!tail. _ = (res,ee with gas_obs := tail)`
        (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [listTheory.APPEND_NIL]))) >>
  simp[]
QED
