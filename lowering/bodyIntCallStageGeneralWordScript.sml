(* Caller-general word staging: forcing is read-only, with no return-PC operand. *)
Theory bodyIntCallStageGeneralWord
Ancestors
  bodyIntCallStageGeneralInterface bodyIntCallJointForce
  bodyIntCallWindowStorage bodyIntCallForcingReadOnly exprSimWordArgs
  exprLoweringProps loweringPosts freshWrites intCallFrame bodyMemoryDefs stmtSimProps
  exprSimBopRestWordBasics gasOutcome gasSummaryCompose exprSimUnwrap
  fragExec exprSimMemorySource exprSimSource valueEncodingTyping exprSimMemDefs

Theorem stage_resources_readonly:
  stage_resources ctx func cx lo prot staged reserved morig oorig rb
    ce env es sa s /\ sa.cs_next_var <= sb.cs_next_var /\
  stmt_state_rel ctx func ce cx es u /\
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!n p k. local_region ce es.scopes u n p k <=>
             local_region ce es.scopes s n p k) /\
  (!q. reserved q ==> eval_operand q u = eval_operand q s) ==>
  stage_resources ctx func cx lo prot staged reserved morig oorig rb
    ce env es sb u
Proof
  strip_tac >> fs[stage_resources_def] >> rpt conj_tac >> simp[]
  >- metis_tac[local_ptrs_reserved_next_var]
  >- (gvs[allocas_above_def] >> metis_tac[])
  >- metis_tac[not_fresh_at_mono]
  >- metis_tac[]
  >- (irule ret_pc_ok_frame >> qexistsl [`ce`, `s`, `sa`] >> simp[])
  >- (irule return_buf_frame_frame >> qexistsl [`ce`, `s`, `sa`] >> simp[]) >>
  metis_tac[]
QED

Theorem stage_cont_readonly_suffix:
  stage_cont ctx func cx lo prot staged reserved morig oorig rb
    ce env es sa s ee sm t /\ sa.cs_next_var <= sm.cs_next_var /\
  sm.cs_next_var <= sb.cs_next_var /\
  stmt_state_rel ctx func ce cx ee u /\
  u.vs_memory = t.vs_memory /\ u.vs_allocas = t.vs_allocas /\
  u.vs_alloca_next = t.vs_alloca_next /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x t) /\
  (!n p k. local_region ce ee.scopes u n p k <=>
             local_region ce ee.scopes t n p k) /\
  (!q. reserved q ==> eval_operand q u = eval_operand q t) /\
  ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
  u.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  stage_cont ctx func cx lo prot staged reserved morig oorig rb
    ce env es sa s ee sb u
Proof
  strip_tac >> fs[stage_cont_def] >> simp[] >> conj_tac
  >- (irule stage_resources_readonly >>
      simp[] >> qexistsl [`t`, `sm`] >> simp[]) >>
  irule wb_frame_readonly_tail >> goal_assum (drule_at Any) >>
  qexists `sm` >> simp[]
QED

Theorem stage_word_value_forcing:
  unwrap_value ce vv sm = (op,sb) /\ vv_holds ce cx ty r vv ee t /\
  read_result cx r ee = (INL v,ee) /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  fn_has_code sm sb func /\
  stage_cont ctx func cx lo prot staged reserved morig oorig rb
    ce env es sa s ee sm t /\ sa.cs_next_var <= sm.cs_next_var /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) ==>
  ?u. gas_marked_path F ctx func t 0 (OK u) /\
    expr_val_rel cx ty v op u /\
    (!x. op = Var x ==> not_fresh_at sb x) /\
    stage_cont ctx func cx lo prot staged reserved morig oorig rb
      ce env es sa s ee sb u
Proof
  strip_tac >>
  `!x. op = Var x ==> not_fresh_at sb x` by
    metis_tac[unwrap_value_operand_reserved] >>
  drule_all vv_holds_materialise >> strip_tac >>
  Cases_on `vv`
  >- (drule (SRULE [] protected_identity_value_forcing) >>
      disch_then drule >> fs[stage_cont_def] >>
      disch_then (qspecl_then [`func`, `ctx`] strip_assume_tac) >>
      qexists `t` >> gvs[stage_cont_def]) >>
  rename1 `LocatedValue ann p` >>
  `sm.cs_next_var <= sb.cs_next_var` by
    (mp_tac (Q.SPECL [`ce`, `LocatedValue ann p`, `sm`] ci_mono_unwrap_value) >>
     simp[ci_mono_def]) >>
  `stmt_state_rel ctx func ce cx ee t /\ local_ptrs_reserved ce sm /\
   (!q x. reserved q /\ q = Var x ==> not_fresh_at sm x) /\
   ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
   t.vs_inst_idx = LENGTH sm.cs_current_insts` by
    fs[stage_cont_def, stage_resources_def] >>
  drule_all protected_word_value_frame_forcing >>
  disch_then (qspec_then `ee.scopes` strip_assume_tac) >>
  `u.vs_memory = t.vs_memory /\ u.vs_allocas = t.vs_allocas /\
   u.vs_alloca_next = t.vs_alloca_next` by
    (rpt conj_tac >> qpat_assum `u = _` (fn th => simp[Once th])) >>
  qexists `u` >> simp[] >> irule stage_cont_readonly_suffix >>
  simp[] >> qexistsl [`sm`, `t`] >> simp[]
QED

Theorem stage_word_arg_outcome:
  body_inv tops ctx ce cx /\
  stage_producer tops ctx func cx lo prot staged reserved morig oorig rb e /\
  expr_body_pre ce cx env e es /\ is_word_type ty /\
  type_widens_to (get_tenv cx) (expr_type e) ty /\
  evaluate_type (get_tenv cx) ty = SOME dtv /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  unwrap_value ce vv sm = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stage_resources ctx func cx lo prot staged reserved morig oorig rb
    ce env es sa t /\ ~t.vs_halted /\
  t.vs_current_bb = sa.cs_current_bb /\
  t.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (read_result cx)) (es,t)
    (\res ee u. ?v w. res = INL v /\ eval_operand op u = SOME w /\
      (!x. op = Var x ==> not_fresh_at sb x) /\
      w = typed_val_to_w256 dtv v /\ val_wf dtv v /\
      stage_cont ctx func cx lo prot staged reserved morig oorig rb
        ce env es sa t ee sb u /\ MAP FDOM es.scopes = MAP FDOM ee.scopes)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `expr_type e = ty` by metis_tac[compileEnvTheory.type_widens_to_word] >>
  `post_value_type ce e = ty` by simp[] >>
  drule compile_expr_extends >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    (irule forced_expr_admissible_raw >>
     metis_tac[expr_body_pre_gas_admissible]) >>
  qpat_x_assum `stage_producer _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[stage_producer_def] >> disch_then drule_all >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` DISJ_CASES_TAC) >> qexists `marks`
  >- (disj1_tac >>
      rewrite_tac[gasSummaryTheory.gas_summary_at_def] >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gasSummaryTheory.gas_summary_at_def] >>
      disch_then (qx_choose_then `res` (qx_choose_then `mid`
        (qx_choose_then `r` strip_assume_tac)))
      >- suspend "normal" >>
      Cases_on `res` >> gvs[] >> rename1 `expr_exit (INR exc) r` >>
      qexistsl [`INR exc`, `mid`, `r`] >> conj_tac
      >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      simp[] >> metis_tac[expr_exit_INR_type]) >>
  disj2_tac >>
  qpat_x_assum `?err ee leaf finish. _` (qx_choose_then `err`
    (qx_choose_then `ee` (qx_choose_then `leaf`
      (qx_choose_then `fin` assume_tac)))) >>
  drule force_exempt_cert >> disch_then (qspec_then `cx` assume_tac) >>
  qexistsl [`err`, `ee`, `leaf`, `fin`] >> simp[]
QED

Resume stage_word_arg_outcome[normal]:
  gvs[] >>
  drule rest_word_vv_read_suffix >> strip_tac >>
  `read_result cx tv (mid with gas_obs := []) =
     (INL v,mid with gas_obs := [])` by
    (first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_at (Pat `stage_cont _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    stage_word_value_forcing >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
    (fs[stage_cont_def, wb_frame_def, locals_kept_def] >> metis_tac[]) >>
  `value_runtime_typed env (expr_type e) v` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gasSummaryTheory.gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` assume_tac) >>
     irule exprSimHypsTheory.memory_rhs_read_annotation_typed >>
     qexistsl [`ce`, `cx`,
       `es with gas_obs := gas_explicit marks t.vs_gas_readings ++ []`,
       `mid with gas_obs := []`] >>
     fs[expr_body_pre_gas_obs, vyperStateTheory.bind_def, SF ETA_ss]) >>
  `env.type_defs = get_tenv cx` by
    fs[stage_resources_def, exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `val_wf dtv v` by
    (irule (cj 1 valueEncodingTypingTheory.value_has_type_val_wf) >>
     gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def]) >>
  qexistsl [`INL v`, `mid with gas_obs := []`, `OK u`] >> conj_tac
  >- (irule gas_marked_exec_bind_zero_suffix >> goal_assum (drule_at Any) >>
      qexistsl [`mid`, `tv`] >> simp[]) >>
  gvs[expr_val_rel_def]
QED

Finalise stage_word_arg_outcome
