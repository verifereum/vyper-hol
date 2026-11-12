(* Argument-list composition on the counted head's actual endpoint. *)
Theory bodyIntCallArgList
Ancestors
  bodyIntCallHeldArgs bodyIntCallHeadProducer bodyIntCallExecutionFrame
  bodyIntCallArgEligibility bodyIntCallSourceFrame bodyIntCallProducerInterface
  bodySim exprSimHyps exprSimHypsDefs exprSimSource exprSimProps
  exprSimSubscriptMap exprLoweringProps exprLowering compileEnv fragExec
  gasSummary gasOutcome gasContext stmtSimForRounds vyperInterpreter vyperState
  loweringPosts stmtLoweringMono list pair

Theorem intcall_marked_held_extend:
  body_results_ok cx (e::args) /\
  intcall_held_args ce cx a sm es s H /\
  a.cs_next_id <= sm.cs_next_id /\
  expr_body_pre ce cx env e es /\ ~expr_has_effect e /\
  gas_marked_exec F (ctx,func) (eval_expr cx e) (es,s) marks
    (INL raw) mid (OK t) /\
  compile_expr ce (expr_type e) e sm = (vv,sn) /\
  local_ptrs_reserved ce sm /\ stmt_state_rel ctx func ce cx es s /\
  vv_post ctx func ce cx e es sm sn s (mid with gas_obs := []) raw vv t /\
  intcall_vv_provenance ce cx (expr_type e) sm sn
    (mid with gas_obs := []) raw vv t ==>
  intcall_held_args ce cx a sn (mid with gas_obs := []) t
    (H ++ [(expr_type e,raw,vv)]) /\
  expr_sim_inv ce cx env (mid with gas_obs := []) /\
  (mid with gas_obs := []) = es with
    <|outcomes := mid.outcomes; gas_obs := []|> /\
  body_results_ok cx args
Proof
  strip_tac >>
  `t.vs_labels = s.vs_labels` by metis_tac[intcall_marked_exec_labels] >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >> fs[] >>
  `expr_body_pre ce cx env e
    (es with gas_obs := gas_explicit marks s.vs_gas_readings)` by simp[] >>
  `stmt_state_rel ctx func ce cx
    (es with gas_obs := gas_explicit marks s.vs_gas_readings) s` by simp[] >>
  `vv_post ctx func ce cx e
    (es with gas_obs := gas_explicit marks s.vs_gas_readings)
    sm sn s (mid with gas_obs := []) raw vv t` by
    simp[vv_post_initial_gas] >>
  `intcall_held_args ce cx a sm
    (es with gas_obs := gas_explicit marks s.vs_gas_readings) s H` by simp[] >>
  drule_at (Pat `eval_expr _ _ _ = _`) intcall_held_args_extend >>
  simp[] >> disch_then drule_all >> strip_tac >>
  drule_all exprSimSourceTheory.expr_body_pre_eval_result >> strip_tac >>
  drule_all effect_free_eval_expr_outcomes >> strip_tac >>
  fs[] >> metis_tac[body_results_success_tail]
QED

Theorem intcall_args_accumulated:
  !args H a sm es s vals sn k.
  body_inv tops ctx ce cx /\ body_results_ok cx args /\
  EVERY (\e. expr_body_pre ce cx env e es /\ ~expr_has_effect e) args /\
  expr_sim_inv ce cx env es /\
  compile_multi_vvs compile_expr ce args sm = (vals,sn) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ stmt_state_rel ctx func ce cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  a.cs_next_id <= sm.cs_next_id /\ intcall_held_args ce cx a sm es s H /\
  gas_admissible (bind (eval_expr_results cx args) k) expr_vv_res_ok es /\
  (!res ee r. expr_exit res r ==> R res ee r) /\
  (!raws ee t. LENGTH raws = LENGTH args /\ LENGTH vals = LENGTH args /\
    intcall_held_args ce cx a sn ee t
      (H ++ MAP (\(e,(raw,vv)). (expr_type e,raw,vv))
        (ZIP (args,ZIP (raws,vals)))) /\
    expr_sim_inv ce cx env ee /\ stmt_state_rel ctx func ce cx ee t /\
    ee = es with <|outcomes := ee.outcomes; gas_obs := ee.gas_obs|> /\
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

Resume intcall_args_accumulated[tail]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  `intcall_vv_provenance ce cx (expr_type h) sm sh
    (mid with gas_obs := []) v hv t` by simp[] >>
  drule_all intcall_marked_held_extend >> strip_tac >>
  `stmt_state_rel ctx func ce cx (mid with gas_obs := []) t` by
    fs[vv_post_def] >>
  `~t.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     drule stmtSimAugAssignPlaceMemoryTheory.aug_place_marked_path_not_halted >>
     simp[]) >>
  `local_ptrs_reserved ce sh` by metis_tac[local_ptrs_reserved_next_var] >>
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
    [`H ++ [(expr_type h,v,hv)]`,`a`,`sh`,`mid with gas_obs := []`,
     `t`,`vs`,`sn`,`\raws. k (v::raws)`] mp_tac) >>
  simp[] >> impl_tac >- suspend "assemble" >> simp[]
QED

Resume intcall_args_accumulated[assemble]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!raws ee t. _` irule >>
  simp[] >> reverse conj_tac
  >- fs[intcall_held_args_def] >>
  qpat_x_assum `(_ with gas_obs := []) = _` mp_tac >>
  qpat_x_assum `ee = _` mp_tac >>
  simp[evaluation_state_component_equality]
QED

Finalise intcall_args_accumulated

(* Empty initial accumulator: all argument witnesses share this endpoint. *)
Theorem intcall_args_then_outcome:
  body_inv tops ctx ce cx /\ body_results_ok cx args /\
  EVERY (\e. expr_body_pre ce cx env e es /\ ~expr_has_effect e) args /\
  expr_sim_inv ce cx env es /\
  compile_multi_vvs compile_expr ce args sm = (vals,sn) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ stmt_state_rel ctx func ce cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  gas_admissible (bind (eval_expr_results cx args) k) expr_vv_res_ok es /\
  (!res ee r. expr_exit res r ==> R res ee r) /\
  (!raws ee t. LENGTH raws = LENGTH args /\ LENGTH vals = LENGTH args /\
    intcall_held_args ce cx sm sn ee t
      (MAP (\(e,(raw,vv)). (expr_type e,raw,vv))
        (ZIP (args,ZIP (raws,vals)))) /\
    expr_sim_inv ce cx env ee /\ stmt_state_rel ctx func ce cx ee t /\
    ee = es with <|outcomes := ee.outcomes; gas_obs := ee.gas_obs|> /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func) (k raws) (ee,t) Q R) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr_results cx args) k) (es,s) Q R
Proof
  strip_tac >> irule intcall_args_accumulated >>
  simp[] >> qexistsl_tac [`[]`,`sm`] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem intcall_held_args_index:
  LENGTH raws = LENGTH args /\ LENGTH vals = LENGTH args /\
  intcall_held_args ce cx a sn ee t
    (MAP (\(e,(raw,vv)). (expr_type e,raw,vv))
      (ZIP (args,ZIP (raws,vals)))) /\ i < LENGTH args ==>
  vv_holds ce cx (expr_type (EL i args)) (EL i raws) (EL i vals) ee t /\
  vv_at ce cx (expr_type (EL i args)) a sn ee (EL i raws) (EL i vals) t /\
  intcall_vv_provenance ce cx (expr_type (EL i args)) a sn ee
    (EL i raws) (EL i vals) t /\
  vv_storage_live cx (EL i vals) ee t /\
  (!v tv. read_result cx (EL i raws) ee = (INL v,ee) /\
          evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME tv ==>
          val_wf tv v /\ value_has_type tv v) /\
  (!x. vv_operand (EL i vals) = Var x ==> not_fresh_at sn x)
Proof
  strip_tac >> irule intcall_held_args_member >>
  goal_assum (drule_at Any) >>
  simp[MEM_MAP, EXISTS_PROD, MEM_ZIP] >>
  qexists_tac `EL i args` >> simp[] >>
  qexists_tac `i` >> simp[EL_ZIP]
QED
