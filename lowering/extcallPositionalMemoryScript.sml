(* Raw external-call positional results, deliberately not read here. *)
Theory extcallPositionalMemory
Ancestors
  exprSimMemDefs exprSimDefs exprSimSubscriptMap exprLoweringProps fragExec
  gasOutcome gasSummaryCompose fragGasPath allocaHistory
  exprLowering compileEnv loweringPosts vyperInterpreter vyperState list
Libs
  monadsyntax

Theorem extcall_multi_vvs_grows[local]:
  !es sa vvs sb.
    compile_multi_vvs compile_expr ce es sa = (vvs,sb) ==>
    cs_extends sa sb
Proof
  Induct >> simp[compile_multi_vvs_def, comp_return_def, comp_bind_def,
                 cs_extends_refl] >>
  rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  drule (cj 1 compile_expr_grows) >> strip_tac >>
  metis_tac[cs_extends_trans]
QED

Theorem extcall_positional_mem_cps:
  !es sa vvs sb ars avvs ee s.
    compile_multi_vvs compile_expr ce es sa = (vvs,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    P ars avvs ee s sa /\
    (!rs vs st t sc.
       P rs vs st t sc ==>
       local_ptrs_reserved ce sc /\
       stmt_state_rel ctx func ce cx st t /\ alloca_history func t /\
       ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
       t.vs_inst_idx = LENGTH sc.cs_current_insts) /\
    (!e rs vs st t sc.
       MEM e es /\ P rs vs st t sc ==>
       expr_vv_sim_mem ctx func ce cx (expr_type e) e st /\
       gas_admissible (eval_expr cx e) expr_vv_res_ok st) /\
    (!e rs vs st t sc sn vv tv fin u.
       MEM e es /\ P rs vs st t sc /\
       compile_expr ce (expr_type e) e sc = (vv,sn) /\
       vv_post ctx func ce cx e st sc sn t fin tv vv u /\
       vv_store_bound cx (expr_type e) (lowered_value_type ce e) fin tv vv u /\
       u.vs_current_bb = sn.cs_current_bb /\
       u.vs_inst_idx = LENGTH sn.cs_current_insts /\
       alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next ==>
       P (rs ++ [tv]) (vs ++ [vv]) fin u sn) /\
    (!rs vs st t.
       P rs vs st t sb ==>
       gas_outcome T (cx_tops cx) (ctx,func) (k rs vs) (st,t) Q (\res ee r. expr_exit res r)) ==>
    gas_outcome T (cx_tops cx) (ctx,func)
      (bind (eval_expr_results cx es)
        (\rs. k (ars ++ rs) (avvs ++ vvs))) (ee,s) Q (\res ee r. expr_exit res r)
Proof
  Induct
  >- (simp[compile_multi_vvs_def, comp_return_def, evaluate_def,
           bind_return] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_multi_vvs _ _ _ _ = _` mp_tac >>
  simp[compile_multi_vvs_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_expr ce (expr_type h) h sa = (vv,sm)` >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[cj 1 compile_expr_grows, extcall_multi_vvs_grows] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `expr_vv_sim_mem ctx func ce cx (expr_type h) h ee /\
   gas_admissible (eval_expr cx h) expr_vv_res_ok ee` by metis_tac[MEM] >>
  `local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx ee s /\
   alloca_history func s /\ ~s.vs_halted /\
   s.vs_current_bb = sa.cs_current_bb /\
   s.vs_inst_idx = LENGTH sa.cs_current_insts` by metis_tac[] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `s`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_tac >>
  simp[Once evaluate_def, bind_assoc, bind_return] >>
  irule gas_outcome_bind_result_exec >>
  goal_assum (drule_at Any) >> simp[] >> conj_tac
  >- ((Cases >- simp[expr_exit_def]) >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt strip_tac >> gvs[] >>
  `P (ars ++ [v]) (avvs ++ [vv]) (mid with gas_obs := []) t sm` by
    metis_tac[] >>
  qpat_x_assum `!sa' vvs' sb' ars' avvs' ee' s''. _`
    (qspecl_then [`sm`, `rest`, `cs''`, `ars ++ [v]`,
                 `avvs ++ [vv]`, `mid with gas_obs := []`, `t`] mp_tac) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[] >> disch_then irule >>
  rpt conj_tac >> metis_tac[]
QED
