(* Requests in a keyword operand precede the nonword default's materialization. *)
Theory s1PrefixExtCallKeywordHead
Ancestors
  s1PrefixPreds s1PrefixDefs s1PrefixOfVV bodyFullExtCallKeywordList
  exprSimHyps exprSimSource gasShadowCompileStmtHelpers gasShadowCompileBase
  exprLoweringProps fragExec gasShadowState exprLowering compileEnv
  exprSimUnwrap vyperTypeSystem entryReachBodyFirstEmissionExprSupport

Theorem extcall_keyword_head_prefix:
  body_expr_full_ok cx e /\ body_expr_prefix_ok cx e /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env e es /\
  expr_type e = ext_call_kw_type rt k /\
  compile_ext_call_kwarg compile_expr cenv rt k e sa = ((op,dt),sb) /\
  compile_ext_call_kwarg compile_expr (gas_shadow_env T cenv) rt k (gas_shadow_expr e)
    shadow_sa = ((op,dt),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  Cases_on `k = EKDefault /\ ~is_word_type rt`
  >- (gvs[] >>
      qpat_x_assum `expr_type e = _` kall_tac >>
      Cases_on `compile_expr cenv (expr_type e) e sa` >>
      rename1 `compile_expr cenv (expr_type e) e sa = (vv,sm)` >>
      Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e)
        (gas_shadow_expr e) shadow_sa` >>
      rename1 `compile_expr _ _ (gas_shadow_expr e) shadow_sa = (sv,shadow_sm)` >>
      `sv = vv /\ gas_shadow_state sm shadow_sm` by
        (`gas_shadow_compiles (compile_expr cenv (expr_type e) e)
            (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
           irule gas_shadow_stmt_compile_expr_env >>
         pop_assum (qspecl_then [`sa`,`shadow_sa`] mp_tac o
           REWRITE_RULE [gas_shadow_compiles_def]) >> simp[]) >>
      qpat_x_assum `sv = vv` SUBST_ALL_TAC >>
      Cases_on `compile_materialize_vv cenv (lowered_value_type cenv e) vv sm` >>
      Cases_on `compile_materialize_vv cenv (lowered_value_type cenv e) vv shadow_sm` >>
      gvs[compile_ext_call_kwarg_def, comp_bind_def, comp_return_def] >>
      `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
        (imp_res_tac compile_expr_extends >>
         imp_res_tac (cj 1 first_emission_materialize_vv) >>
         metis_tac[fn_has_code_split]) >>
      `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx (expr_type e) e es` by
        metis_tac[CONJUNCT1 body_expr_prefix_ok_def] >>
      `expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx (expr_type e) e es (st0,sa,sm,shadow_sa,shadow_sm,vv,s0,G0,tn0)` by
        (simp[expr_vv_sim_full_pre_def] >>
         metis_tac[expr_body_pre_vv_gas_admissible]) >>
      simp[gas_prefix_full_bind_read_result] >>
      qpat_assum `expr_vv_sim_prefix _ _ _ _ _ _`
        (drule_then ACCEPT_TAC o REWRITE_RULE [expr_vv_sim_prefix_def])) >>
  `lower_value compile_expr cenv (ext_call_kw_type rt k) e sa = (op,sb) /\
   lower_value compile_expr (gas_shadow_env T cenv) (ext_call_kw_type rt k)
     (gas_shadow_expr e) shadow_sa = (op,shadow_sb)` by
    (Cases_on `lower_value compile_expr cenv (ext_call_kw_type rt k) e sa` >>
     Cases_on `lower_value compile_expr (gas_shadow_env T cenv)
        (ext_call_kw_type rt k) (gas_shadow_expr e) shadow_sa` >>
     Cases_on `k` >>
     gvs[ext_call_kw_type_def, compile_ext_call_kwarg_def, comp_bind_def, comp_return_def]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (ext_call_kw_type rt k) e es` by
    metis_tac[CONJUNCT1 body_expr_prefix_ok_def] >>
  `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (ext_call_kw_type rt k) e es (st0,sa,sb,shadow_sa,shadow_sb,op,s0,G0,tn0)` by
    (simp[expr_sim_full_pre_def] >> metis_tac[expr_body_pre_gas_admissible]) >>
  qpat_assum `expr_sim_prefix _ _ _ _ _ _`
    (drule_then ACCEPT_TAC o REWRITE_RULE [expr_sim_prefix_def])
QED
