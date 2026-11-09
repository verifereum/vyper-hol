(* Caller framing threaded through the very counted held-list execution. *)
Theory bodyIntCallArgPrefixFrame
Ancestors
  bodyIntCallArgList bodyIntCallHeldArgs bodyIntCallHeadProducer exprSimHyps exprSimSubscriptMap
  bodyIntCallProducerInterface fragExec exprSimWordArgs exprSimSubscriptArrayFrame
  exprSimSource exprSimHypsDefs exprSimProps bodySim stmtLoweringMono
  gasSummary gasOutcome gasContext stmtSimForRounds vyperInterpreter
  vyperState loweringPosts compileEnv exprLoweringProps exprLowering list pair

Theorem intcall_args_frame_accumulated:
  !args H a sm es s vals sn k initial_es sinitial_es.
  body_inv tops ctx ce cx /\ body_results_ok cx args /\
  EVERY (\e. expr_body_pre ce cx env e es /\ ~expr_has_effect e) args /\
  expr_sim_inv ce cx env es /\
  compile_multi_vvs compile_expr ce args sm = (vals,sn) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ stmt_state_rel ctx func ce cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  a.cs_next_id <= sm.cs_next_id /\ a.cs_next_var <= sm.cs_next_var /\
  intcall_held_args ce cx a sm es s H /\
  stmt_state_rel ctx func ce cx initial_es sinitial_es /\ local_ptrs_reserved ce a /\
  es.scopes = initial_es.scopes /\ wb_frame ce initial_es a sinitial_es s /\
  gas_admissible (bind (eval_expr_results cx args) k) expr_vv_res_ok es /\
  (!res ee r. expr_exit res r ==> R res ee r) /\
  (!raws ee t. LENGTH raws = LENGTH args /\ LENGTH vals = LENGTH args /\
    intcall_held_args ce cx a sn ee t
      (H ++ MAP (\(e,(raw,vv)). (expr_type e,raw,vv))
        (ZIP (args,ZIP (raws,vals)))) /\
    expr_sim_inv ce cx env ee /\ stmt_state_rel ctx func ce cx ee t /\
    ee = es with <|outcomes := ee.outcomes; gas_obs := ee.gas_obs|> /\
    wb_frame ce initial_es a sinitial_es t /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func) (k raws) (ee,t) Q R) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr_results cx args) k) (es,s) Q R
Proof
  Induct >> rpt gen_tac
  >- (simp[compile_multi_vvs_def, comp_return_def] >> strip_tac >> gvs[] >>
      simp[Once evaluate_def, bind_return] >> first_x_assum irule >>
      simp[GSYM evaluation_state_component_equality]) >>
  strip_tac >>
  Cases_on `compile_expr ce (expr_type h) h sm` >>
  rename1 `compile_expr ce (expr_type h) h sm = (hv,sh)` >>
  Cases_on `compile_multi_vvs compile_expr ce args sh` >>
  rename1 `compile_multi_vvs compile_expr ce args sh = (vs,sn1)` >>
  gvs[compile_multi_vvs_def, comp_bind_def, comp_return_def] >>
  `ci_mono sh sn` by
    (qspecl_then [`compile_expr`,`ce`,`args`,`sh`] mp_tac
      ci_mono_compile_multi_vvs >> simp[cj 1 ci_mono_compile_expr_sa]) >>
  drule (cj 1 compile_expr_grows) >> strip_tac >>
  `fn_has_code sm sh func /\ fn_has_code sh sn func` by
    (irule fn_has_code_split >> gvs[ci_mono_def]) >>
  `gas_admissible (eval_expr cx h) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  `body_expr_ok cx h` by gvs[body_results_ok_def] >>
  drule_all intcall_arg_provenance >> strip_tac >>
  simp[Once evaluate_def, bind_assoc, bind_return] >>
  irule gas_outcome_bind_result_exec >> goal_assum (drule_at Any) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_def]) >>
  conj_tac >- suspend "tail" >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Resume intcall_args_frame_accumulated[tail]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  `intcall_vv_provenance ce cx (expr_type h) sm sh
    (mid with gas_obs := []) v hv t` by simp[] >>
  drule_all intcall_marked_held_extend >> strip_tac >>
  `stmt_state_rel ctx func ce cx (mid with gas_obs := []) t` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[vv_post_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame ce es sm s t` by
    (qpat_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[vv_post_def, wb_frame_def] >> strip_tac >>
     asm_rewrite_tac[]) >>
  `~t.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     drule stmtSimAugAssignPlaceMemoryTheory.aug_place_marked_path_not_halted >>
     simp[]) >>
  `local_ptrs_reserved ce sh` by metis_tac[local_ptrs_reserved_next_var] >>
  `wb_frame ce initial_es a sinitial_es t` by
    (irule wb_frame_trans >>
     simp[] >> conj_tac
     >- (qexistsl_tac [`es`,`sm`,`s`] >> asm_rewrite_tac[]) >>
     metis_tac[]) >>
  `EVERY (\e. expr_body_pre ce cx env e (mid with gas_obs := []) /\
              ~expr_has_effect e) args` by
    (fs[EVERY_MEM, expr_body_pre_def] >> metis_tac[]) >>
  `gas_admissible
     (bind (eval_expr_results cx args) (\raws. k (v::raws)))
     expr_vv_res_ok (mid with gas_obs := [])` by
    (qpat_x_assum `gas_admissible (bind (eval_expr_results cx (h::args)) _) _ _`
       mp_tac >>
     simp[Once evaluate_def, bind_assoc, bind_return] >> strip_tac >>
     drule gas_admissible_bind_tail >>
     disch_then (qspecl_then [`gas_explicit marks s.vs_gas_readings`,`v`,`mid`] mp_tac) >>
     impl_tac >- (fs[gas_marked_exec_def]) >> simp[]) >>
  first_x_assum (qspecl_then
    [`H ++ [(expr_type h,v,hv)]`,`a`,`sh`,`mid with gas_obs := []`] mp_tac) >>
  disch_then (qspecl_then [`t`,`vs`,`sn`,`\raws. k (v::raws)`] mp_tac) >>
  disch_then (qspecl_then [`initial_es`,`sinitial_es`] mp_tac) >>
  simp[] >> impl_tac >- suspend "assemble" >> simp[]
QED

Resume intcall_args_frame_accumulated[assemble]:
  conj_tac >- (gvs[] >>
    qpat_x_assum `(_ with gas_obs := []) = _` mp_tac >>
    simp[evaluation_state_component_equality]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!raws ee t. _` irule >>
  simp[] >> reverse conj_tac
  >- fs[intcall_held_args_def] >>
  qpat_x_assum `(_ with gas_obs := []) = _` mp_tac >>
  qpat_x_assum `ee = _` mp_tac >>
  simp[evaluation_state_component_equality]
QED

Finalise intcall_args_frame_accumulated
