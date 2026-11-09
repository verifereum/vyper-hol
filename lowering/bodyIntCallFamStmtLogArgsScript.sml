(* Resource-carrying counted evaluation of Log arguments. *)
Theory bodyIntCallFamStmtLogArgs
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtLogArgsFrame bodyIntCallFamStmtLogMarked
  exprBopSimProps vyperEvalExprPreservesScopesDom
  bodyIntCallFamStmtLogReady bodyIntCallFamStmtLogPost bodyIntCallFamStmtLogGas
  stmtSimLogArgs stmtSimLogArgsRun stmtSimLogArgsGrowth stmtReasonVvMemory
  gasOutcome gasSummary fragGasPath fragGasMode
  stmtSimDefs loweringPosts exprSimHypsDefs vyperInterpreter vyperState
  list finite_map
Libs
  monadsyntax

Theorem intcall_compile_log_eval_all:
  (!e. intcall_forced_producer fp e) /\
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  EVERY (\e. expr_body_pre ce fp.jc_cx env e es) args /\
  EVERY (supportedExprs$supported_expr fp.jc_tops) args /\
  EVERY (\e. calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e)) args /\
  EVERY supported_scalar_type (MAP expr_type args) /\
  compile_log_eval_all ce args sa = (xs,sb) /\
  gas_admissible (eval_exprs fp.jc_cx args) log_args_res_ok es /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  intcall_joint_res fp ce env es sa s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (eval_exprs fp.jc_cx args) (es,s)
    (\res ee u. ?vs. res = INL vs /\
      log_args_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sb s ee xs vs u /\
      intcall_expr_cont fp ce env es sa s ee sb u /\
      LIST_REL (\ty v. ?tv. evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\ value_has_type tv v) (MAP expr_type args) vs /\
      EVERY (\p. (!z. FST p = Var z ==> not_fresh_at sb z) /\ (!lab. FST p <> Label lab)) xs)
    (\res ee r. expr_exit res r)
Proof
  map_every qid_spec_tac [`s`, `xs`, `sb`, `sa`, `es`] >>
  Induct_on `args`
  >- (rpt gen_tac >> simp[compile_log_eval_all_nil] >> strip_tac >> gvs[] >>
      simp[Once evaluate_def] >>
      pure_rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INL []`, `es with gas_obs := []`, `OK s`] >>
      simp[gas_marked_exec_def, return_def, gas_marked_path_def,
           log_args_post_def, wb_frame_def,
           intcall_expr_cont_def, intcall_joint_res_def] >>
      fs[intcall_joint_res_def] >>
      conj_tac >- (irule (cj 1 gas_path_rules) >> simp[]) >>
      metis_tac[]) >>
  suspend "cons"
QED

Resume intcall_compile_log_eval_all[cons]:
  rpt gen_tac >> simp[EVERY_DEF, MAP, compile_log_eval_all_cons] >>
  strip_tac >> gvs[] >>
  rename1 `lower_value compile_expr ce (expr_type e) e sa = (op,sm)` >>
  `compile_log_eval_all ce [e] sa = ([(op,expr_type e)],sm)` by
    simp[compile_log_eval_all_cons, compile_log_eval_all_nil] >>
  drule_all compile_log_eval_all_grows >> strip_tac >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    (qpat_x_assum `compile_log_eval_all ce [e] _ = _` mp_tac >>
     metis_tac[compile_log_eval_all_grows]) >>
  qpat_assum `compile_log_eval_all ce args sm = _`
    (strip_assume_tac o MATCH_MP compile_log_eval_all_grows) >>
  `fn_has_code sa sm fp.jc_func /\ fn_has_code sm sb fp.jc_func` by
    (irule fragExecTheory.fn_has_code_split >> simp[]) >>
  `gas_admissible (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  qpat_x_assum `!e. intcall_forced_producer fp e` assume_tac >>
  first_assum (qspec_then `e` mp_tac) >>
  rewrite_tac[intcall_forced_producer_def] >>
  disch_then drule_all >> strip_tac >>
  rewrite_tac[stmtSimLogArgsRunTheory.eval_exprs_cons_bind] >>
  irule gas_outcome_bind_value >>
  goal_assum (drule_at Any) >>
  reverse conj_tac
  >- (rpt strip_tac >> Cases_on `res` >>
      fs[exprSimDefsTheory.expr_exit_INL, stmtSimPropsTheory.expr_exit_INR_type]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  suspend "normal"
QED

Resume intcall_compile_log_eval_all[normal]:
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  `intcall_joint_res fp ce env (mid with gas_obs := []) sm t /\ ~t.vs_halted /\
   t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts` by
    fs[intcall_expr_cont_def] >>
  `EVERY (\e. expr_body_pre ce fp.jc_cx env e (mid with gas_obs := [])) args` by
    (fs[EVERY_MEM] >> rpt strip_tac >> irule expr_body_pre_state_transport >>
     conj_tac >- fs[intcall_joint_res_def] >>
     qexists_tac `es` >> simp[]) >>
  `gas_admissible (bind (eval_exprs fp.jc_cx args) (\vs. return (v::vs)))
     log_args_res_ok (mid with gas_obs := [])` by
    (qpat_assum `gas_admissible (eval_exprs _ (_::_)) _ _`
       (mp_tac o REWRITE_RULE [stmtSimLogArgsRunTheory.eval_exprs_cons_bind]) >>
     disch_then (mp_then Any mp_tac stmtSimForRoundsTheory.gas_admissible_bind_tail) >>
     disch_then (qspecl_then [`gas_explicit marks s.vs_gas_readings`, `v`, `mid`] mp_tac) >>
     fs[gas_marked_exec_def]) >>
  `gas_admissible (eval_exprs fp.jc_cx args) log_args_res_ok (mid with gas_obs := [])` by
    (qpat_x_assum `gas_admissible (bind _ _) _ _` mp_tac >>
     simp[gasContextTheory.gas_admissible_def] >> strip_tac >>
     rpt gen_tac >> strip_tac >>
     first_x_assum (qspec_then `gs` mp_tac) >>
     simp[bind_def] >>
     fs[stmtSimLogArgsRunTheory.log_args_res_ok_def] >>
     Cases_on `res` >> simp[return_def, stmtSimLogArgsRunTheory.log_args_res_ok_def]) >>
  qpat_assum `!es sa sb xs s. _`
    (qspecl_then [`mid with gas_obs := []`, `sm`, `sb`, `ys`, `t`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_tac >>
  irule gas_outcome_marked_return_map >> goal_assum (drule_at Any) >>
  reverse conj_tac
  >- (rpt gen_tac >> simp[exprSimDefsTheory.expr_exit_success_map]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  suspend "posts"
QED

Resume intcall_compile_log_eval_all[posts]:
  qpat_x_assum `!es sa sb xs s. _` kall_tac >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
    (metis_tac[bop_marked_scopes_dom]) >>
  `MAP FDOM (mid with gas_obs := []).scopes =
   MAP FDOM (mid' with gas_obs := []).scopes` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >>
     strip_tac >> drule eval_exprs_preserves_scopes_dom >> simp[]) >>
  `post_value_type ce e = expr_type e` by
    metis_tac[log_scalar_post_value_type] >>
  `?bt. expr_type e = BaseT bt` by metis_tac[log_scalar_base] >>
  `expr_post fp.jc_ctx fp.jc_func ce fp.jc_cx e es sa sm s
     (mid with gas_obs := []) v op t` by
    (irule intcall_forced_expr_post >> simp[] >> metis_tac[]) >>
  `!lab. op <> Label lab` by
    (irule exprReasonOperandTheory.lower_compile_expr_not_label >>
     goal_assum (drule_at Any) >>
     qexists_tac `env` >> fs[expr_body_pre_def, expr_sim_inv_def]) >>
  conj_tac
  >- (irule log_args_post_cons >>
      goal_assum (drule_at Any) >>
      fs[intcall_joint_res_def] >>
      conj_tac >- (qexistsl_tac [`env`, `es`] >> simp[]) >>
      qexistsl_tac [`mid with gas_obs := []`, `sm`, `t`] >> simp[]) >>
  conj_tac
  >- (irule intcall_expr_cont_trans >>
      conj_tac >- simp[] >>
      qexistsl_tac [`mid with gas_obs := []`, `sm`, `t`] >> simp[]) >>
  reverse conj_tac
  >- (simp[] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  qpat_x_assum `gas_marked_exec _ _ (bind (eval_expr _ _) _) _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >> strip_tac >>
  `expr_body_pre ce fp.jc_cx env e
     (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ [])` by simp[] >>
  `value_runtime_typed env (expr_type e) v` by
    metis_tac[bodySimStmtCasesTheory.expr_body_pre_eval] >>
  fs[vyperTypeExprSoundnessTheory.value_runtime_typed_def,
     expr_body_pre_def, expr_sim_inv_def,
     vyperTypeInvariantsTheory.env_consistent_def,
     vyperTypeInvariantsTheory.env_context_consistent_def] >> metis_tac[]
QED

Finalise intcall_compile_log_eval_all
