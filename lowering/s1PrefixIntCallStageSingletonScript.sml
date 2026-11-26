(* A singleton staged actual has the same source requests as its child. *)
Theory s1PrefixIntCallStageSingleton
Ancestors
  s1PrefixDefs s1PrefixPreds s1PrefixOfVV exprSimWordArgs exprSimSource exprSimMemorySource
  gasShadowCompileCallSupport gasShadowCompileStmtHelpers bodyFullShared
  exprSimUnwrap exprLowering exprLoweringProps compileEnv fragExec fragFuel
  gasShadowState gasShadowCompile vyperInterpreter vyperState pair list

Theorem compile_stage_intcall_args_cons_cut:
  compile_stage_intcall_args cfn ce (e::es) (flag::flags) (dty::dtys) =
  comp_bind (compile_stage_intcall_args cfn ce [e] [flag] [dty])
    (\hs. comp_bind (compile_stage_intcall_args cfn ce es flags dtys)
      (\rest. comp_return (hs ++ rest)))
Proof
  Cases_on `flag` >>
  simp[compile_stage_intcall_args_def, comp_ignore_bind_def, comp_bind_assoc,
       comp_bind_return]
QED

Theorem compile_stage_intcall_args_singleton_value[local]:
  compile_stage_intcall_args compile_expr ce [e] [T] [dty] =
  comp_bind (lower_value compile_expr ce (expr_type e) e)
    (\op. comp_return [op])
Proof
  simp[compile_stage_intcall_args_def, lower_value_def, comp_bind_assoc,
       comp_bind_return]
QED

Theorem compile_stage_intcall_args_singleton_from_vv:
  cfn ce (expr_type e) e si = (vv,ci) ==>
  compile_stage_intcall_args cfn ce [e] [flag] [dty] si =
  compile_stage_intcall_args (\_ _ _. comp_return vv) ce [e] [flag] [dty] ci
Proof
  Cases_on `flag` >>
  simp[compile_stage_intcall_args_def, comp_bind_def, comp_return_def]
QED

Theorem compile_stage_intcall_args_singleton_shape[local]:
  ?h sf. compile_stage_intcall_args cfn ce [e] [flag] [dty] si = ([h],sf)
Proof
  Cases_on `flag` >>
  simp[compile_stage_intcall_args_def, comp_ignore_bind_def, comp_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> simp[])
QED

Theorem intcall_stage_cons_singleton_cut:
  compile_stage_intcall_args compile_expr ce (e::es) (flag::flags) (dty::dtys) si =
    (ops,sf) /\
  compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
    (MAP gas_shadow_expr (e::es)) (flag::flags) (dty::dtys) shadow_si =
    (ops,shadow_sf) /\
  gas_shadow_state si shadow_si /\
  fn_has_code si sf func /\ fn_has_code shadow_si shadow_sf shadow_func ==>
  ?h sm shadow_sm rest.
    compile_stage_intcall_args compile_expr ce [e] [flag] [dty] si = ([h],sm) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
      [gas_shadow_expr e] [flag] [dty] shadow_si = ([h],shadow_sm) /\
    compile_stage_intcall_args compile_expr ce es flags dtys sm = (rest,sf) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
      (MAP gas_shadow_expr es) flags dtys shadow_sm = (rest,shadow_sf) /\
    ops = h::rest /\ gas_shadow_state sm shadow_sm /\
    fn_has_code si sm func /\ fn_has_code sm sf func /\
    fn_has_code shadow_si shadow_sm shadow_func /\
    fn_has_code shadow_sm shadow_sf shadow_func
Proof
  strip_tac >>
  `!xs sh. gas_shadow_compiles
     (compile_stage_intcall_args compile_expr ce xs [flag] [dty])
     (compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
       (if sh then MAP gas_shadow_expr xs else xs) [flag] [dty])` by
    (rpt gen_tac >> irule gas_shadow_compiles_stage_intcall_args_env >>
     simp[cj 1 gas_shadow_compile_expr_env]) >>
  pop_assum (qspecl_then [`[e]`,`T`] mp_tac) >> simp[] >> strip_tac >>
  `?h sm. compile_stage_intcall_args compile_expr ce [e] [flag] [dty] si = ([h],sm)` by
    simp[compile_stage_intcall_args_singleton_shape] >>
  Cases_on `compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
    [gas_shadow_expr e] [flag] [dty] shadow_si` >>
  rename1 `_ = (shadow_ops,shadow_sm)` >>
  drule_all gas_shadow_step >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_stage_intcall_args _ _ (e::es) _ _ si = _`
    (mp_tac o ONCE_REWRITE_RULE[compile_stage_intcall_args_cons_cut]) >>
  qpat_x_assum `compile_stage_intcall_args _ _ (gas_shadow_expr e::MAP gas_shadow_expr es) _ _ shadow_si = _`
    (mp_tac o ONCE_REWRITE_RULE[compile_stage_intcall_args_cons_cut]) >>
  simp[comp_bind_def, comp_return_def] >>
  Cases_on `compile_stage_intcall_args compile_expr ce es flags dtys sm` >>
  Cases_on `compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
    (MAP gas_shadow_expr es) flags dtys shadow_sm` >>
  simp[] >> rpt strip_tac >> gvs[] >>
  (* Split the two function slices at their independently compiled cuts. *)
  `!ce es flags tys si. cs_extends si
    (SND (compile_stage_intcall_args compile_expr ce es flags tys si))` by
    (rpt gen_tac >>
     irule (cj 1 (iffLR ci_mono_def)) >>
     irule ci_mono_compile_stage_intcall_args >> simp[compile_expr_ci_mono]) >>
  metis_tac[fn_has_code_split, SND]
QED

Theorem fn_has_code_intcall_singleton_head:
  compile_expr ce (expr_type e) e si = (vv,ci) /\
  compile_stage_intcall_args compile_expr ce [e] [flag] [dty] si = (hs,sf) /\
  fn_has_code si sf func ==>
  fn_has_code si ci func
Proof
  strip_tac >>
  `cs_extends si ci` by metis_tac[compile_expr_extends] >>
  `ci_mono ci (SND (compile_stage_intcall_args (\_ _ _. comp_return vv)
     ce [e] [flag] [dty] ci))` by
    (irule ci_mono_compile_stage_intcall_args >> simp[ci_mono_comp_return]) >>
  `cs_extends ci sf` by
    (drule compile_stage_intcall_args_singleton_from_vv >>
     disch_then (qspecl_then [`flag`,`dty`] mp_tac) >>
     fs[ci_mono_def] >> metis_tac[SND]) >>
  metis_tac[fn_has_code_split]
QED

Theorem intcall_stage_singleton_prefix_at_cut:
  expr_body_pre ce cx env e esi /\
  (flag ==> expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e esi (st0,si,sf,shadow_si,shadow_sf,h,s,G,tn) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (bind (eval_expr cx e) (read_result cx)) (esi,s,G,tn)) /\
  (~flag ==> !vv ci shadow_ci.
    compile_expr ce (expr_type e) e si = (vv,ci) /\
    compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_si =
      (vv,shadow_ci) /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      ce cx (expr_type e) e esi (st0,si,ci,shadow_si,shadow_ci,vv,s,G,tn) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (eval_expr cx e) (esi,s,G,tn)) /\
  compile_stage_intcall_args compile_expr ce [e] [flag] [dty] si = ([h],sf) /\
  compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
    [gas_shadow_expr e] [flag] [dty] shadow_si = ([h],shadow_sf) /\
  gas_shadow_state si shadow_si /\ gas_shadow_state sf shadow_sf /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code si sf func /\ fn_has_code shadow_si shadow_sf shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce si /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  return_buf_frame d ce si s /\ alloca_history func s /\
  (!H. valid_horizon cx st0 H esi.storage_trace ==>
    stmt_state_rel H ctx func ce cx esi s /\
    storage_well_formed_on cx esi (FST H) /\
    ghost_inv_at (DF H) lo d ce cx esi G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = si.cs_current_bb /\
  s.vs_inst_idx = LENGTH si.cs_current_insts ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (eval_exprs cx [e]) (esi,s,G,tn)
Proof
  strip_tac >>
  `!qe. SND (eval_exprs cx [e] qe) =
        SND (bind (eval_expr cx e) (read_result cx) qe)` by
    (gen_tac >> rewrite_tac[eval_exprs_cons_action] >>
     Cases_on `bind (eval_expr cx e) (read_result cx) qe` >>
     rename1 `_ = (res,mid)` >> Cases_on `res` >>
     simp[bind_def, return_def, eval_exprs_nil]) >>
  drule gas_prefix_full_state_cong >> disch_then (fn th => once_rewrite_tac[th]) >>
  drule expr_body_pre_gas_admissible >> strip_tac >>
  Cases_on `flag` >> fs[]
  >- (`lower_value compile_expr ce (expr_type e) e si = (h,sf)` by
        (qpat_x_assum `compile_stage_intcall_args _ _ _ _ _ si = _` mp_tac >>
         simp[compile_stage_intcall_args_singleton_value, comp_bind_def,
              comp_return_def] >> pairarg_tac >> simp[]) >>
      `lower_value compile_expr (gas_shadow_env T ce) (expr_type e)
         (gas_shadow_expr e) shadow_si = (h,shadow_sf)` by
        (qpat_x_assum `compile_stage_intcall_args _ _ [gas_shadow_expr _] _ _ shadow_si = _` mp_tac >>
         simp[compile_stage_intcall_args_singleton_value, comp_bind_def,
              comp_return_def] >> pairarg_tac >> simp[]) >>
      `expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
         ce cx (expr_type e) e esi (st0,si,sf,shadow_si,shadow_sf,h,s,G,tn)` by
        (simp[expr_sim_full_pre_def] >> metis_tac[]) >>
      first_x_assum irule >> first_assum ACCEPT_TAC) >>
  Cases_on `compile_expr ce (expr_type e) e si` >>
  rename1 `_ = (vv,ci)` >>
  Cases_on `compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_si` >>
  rename1 `compile_expr _ _ (gas_shadow_expr _) _ = (shadow_vv,shadow_ci)` >>
  `gas_shadow_compiles (compile_expr ce (expr_type e) e)
     (compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e))` by
    irule gas_shadow_stmt_compile_expr_env >>
  drule_all gas_shadow_step >> strip_tac >> gvs[] >>
  rename1 `compile_expr _ _ (gas_shadow_expr _) _ = (cvv,shadow_ci)` >>
  `fn_has_code si ci func` by
    (irule fn_has_code_intcall_singleton_head >>
     qpat_assum `compile_stage_intcall_args _ _ [e] _ _ si = _` (irule_at Any) >>
     simp[]) >>
  `fn_has_code shadow_si shadow_ci shadow_func` by
    (irule fn_has_code_intcall_singleton_head >>
     qpat_assum `compile_stage_intcall_args _ _ [gas_shadow_expr _] _ _ shadow_si = _`
       (irule_at Any) >> simp[]) >>
  drule forced_expr_admissible_raw >> strip_tac >>
  `expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     ce cx (expr_type e) e esi (st0,si,ci,shadow_si,shadow_ci,cvv,s,G,tn)` by
    (simp[expr_vv_sim_full_pre_def] >> metis_tac[]) >>
  rewrite_tac[gas_prefix_full_bind_read_result] >>
  first_x_assum irule >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem intcall_stage_singleton_prefix:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env esi /\
  expr_body_pre ce cx env e esi /\ body_expr_prefix_ok cx e /\
  compile_stage_intcall_args compile_expr ce [e] [flag] [dty] si = ([h],sf) /\
  compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
    [gas_shadow_expr e] [flag] [dty] shadow_si = ([h],shadow_sf) /\
  gas_shadow_state si shadow_si /\ gas_shadow_state sf shadow_sf /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code si sf func /\ fn_has_code shadow_si shadow_sf shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce si /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  return_buf_frame d ce si s /\ alloca_history func s /\
  (!H. valid_horizon cx st0 H esi.storage_trace ==>
    stmt_state_rel H ctx func ce cx esi s /\
    storage_well_formed_on cx esi (FST H) /\
    ghost_inv_at (DF H) lo d ce cx esi G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = si.cs_current_bb /\
  s.vs_inst_idx = LENGTH si.cs_current_insts ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (eval_exprs cx [e]) (esi,s,G,tn)
Proof
  strip_tac >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     ce cx (expr_type e) e esi /\
   expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     ce cx (expr_type e) e esi` by
    (qpat_assum `body_expr_prefix_ok cx e`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE[body_expr_prefix_ok_def]) >>
     disch_then drule_all >> simp[]) >>
  irule intcall_stage_singleton_prefix_at_cut >>
  qpat_assum `compile_stage_intcall_args _ _ [e] _ _ si = _` (irule_at Any) >>
  qpat_assum `compile_stage_intcall_args _ _ [gas_shadow_expr e] _ _ shadow_si = _`
    (irule_at Any) >>
  qpat_assum `expr_body_pre ce cx env e esi` (irule_at Any) >>
  qpat_assum `gas_shadow_function func shadow_func` (irule_at Any) >>
  qpat_assum `return_buf_frame d ce si s` (irule_at Any) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  FIRST [qpat_assum `expr_sim_prefix _ _ _ _ _ _`
      (drule_then irule o REWRITE_RULE[expr_sim_prefix_def]),
    qpat_assum `expr_vv_sim_prefix _ _ _ _ _ _`
      (drule_then irule o REWRITE_RULE[expr_vv_sim_prefix_def])]
QED
