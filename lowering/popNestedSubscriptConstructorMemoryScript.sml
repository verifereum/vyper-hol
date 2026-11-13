(* Counted constructor sequencing; endpoint readiness is supplied by callers. *)
Theory popNestedSubscriptConstructorMemory
Ancestors
  popNestedTargetReadinessMemory
  targetPlaceSimMem targetSubscriptSplit targetSubscriptContinuation
  targetPlaceSim targetPlaceSimCasesBase exprSimSubscriptMap exprSimMemDefs
  targetPlaceSimDefs loweringPosts exprLowering exprLoweringProps gasOutcome
  gasSummary exprSimDefs compileEnv vyperAST vyperInterpreter vyperState venomState
  vyperTypeEnv fragExec

Theorem pop_nested_subscript_constructor_mem:
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  target_sim_mem ctx func cenv cx env bt es /\
  (!vt sa sb op s0 bvt rb sm ix sn left pv mid t.
    type_place_target env bt = SOME bvt /\
    subscript_vtype bvt (expr_type e) = SOME vt /\
    compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
    lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
    target_subscript_suffix cenv e rb ix sn = (op,sb) /\
    ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb /\
    fn_has_code sm sn func /\ fn_has_code sn sb func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    gas_admissible (eval_base_place cx (SubscriptTarget bt e)) target_res_ok es /\
    stmt_state_rel ctx func cenv cx es s0 /\
    gas_marked_exec T (ctx,func) (eval_base_place cx bt)
      (es,s0) left (INL pv) mid (OK t) /\
    target_post ctx func cenv cx es sa sm s0 (mid with gas_obs := []) pv bvt rb t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func t ==>
    gas_outcome T (cx_tops cx) (ctx,func)
      (bind (bind (eval_expr cx e) (read_result cx))
        (\key. extend_place cx pv (ValueSubscript key)))
      (mid with gas_obs := [],t)
      (\res ee u. ?pv'. res = INL pv' /\
        target_post ctx func cenv cx es sa sb s0 ee pv' vt op u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next)
      (\res ee r. expr_exit res r)) ==>
  target_sim_mem ctx func cenv cx env (SubscriptTarget bt e) es
Proof
  strip_tac >> rewrite_tac[target_sim_mem_def] >> rpt strip_tac >>
  irule pop_nested_target_outcome_ready_mem >>
  conj_tac >- (qexists `env` >> first_assum ACCEPT_TAC) >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    metis_tac[target_subscript_base_admissible] >>
  `?bvt. type_place_target env bt = SOME bvt /\
    subscript_vtype bvt (expr_type e) = SOME vt` by
    fs[type_place_target_SubscriptTarget] >>
  drule target_subscript_compile_decompose >> strip_tac >>
  drule_all target_subscript_compile_intervals >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func` by
    (irule target_subscript_interval_code >> simp[]) >>
  suspend "bind"
QED

Resume pop_nested_subscript_constructor_mem[bind]:
  `gas_outcome T (cx_tops cx) (ctx,func) (eval_base_place cx bt) (es,s0)
    (\res ee t. ?pv. res = INL pv /\
      target_post ctx func cenv cx es sa sm s0 ee pv bvt rb t /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)` by
    (qpat_x_assum `target_sim_mem _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [target_sim_mem_def]) >>
     disch_then (qspecl_then [`bvt`,`sa`,`sm`,`rb`,`s0`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_tac >>
     irule gas_outcome_post_mono >>
     goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  once_rewrite_tac[evaluate_def] >> rewrite_tac[GSYM bind_assoc] >>
  irule gas_outcome_bind_result_exec >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >>
  reverse conj_tac >- suspend "continue" >>
  rpt strip_tac >> Cases_on `res` >> gvs[oneline expr_exit_def, exit_result_def]
QED

Resume pop_nested_subscript_constructor_mem[continue]:
  simp[] >> reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!vt sa sb op s0 bvt rb sm ix sn left pv mid t. _`
    (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> strip_tac >>
  irule gas_outcome_post_mono >>
  goal_assum (drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)) >>
  rpt strip_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Finalise pop_nested_subscript_constructor_mem
