(* A word argument is a forced producer, since staging is unwrap_value. *)
Theory bodyIntCallStageEndpointWord
Ancestors
  bodyIntCallJointForce bodyIntCallJointContract exprSimSource exprSimMemDefs stmtSimForLoop
  exprBopSimProps exprSimHyps valueEncodingTyping exprLoweringProps

Theorem intcall_stage_word_arg_outcome:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_expr_producer fp e /\
  supportedExprs$supported_expr fp.jc_tops e /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
  expr_body_pre ce fp.jc_cx env e es /\
  is_word_type ty /\
  type_widens_to (get_tenv fp.jc_cx) (expr_type e) ty /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME dtv /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  unwrap_value ce vv sm = (op,sb) /\
  fn_has_code sa sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  intcall_expr_res fp ce env es sa t /\ ~t.vs_halted /\
  t.vs_current_bb = sa.cs_current_bb /\
  t.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (vyperState$bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx)) (es,t)
    (\res ee u. ?v w. res = INL v /\
       eval_operand op u = SOME w /\
       (!x. op = Var x ==> not_fresh_at sb x) /\
       w = typed_val_to_w256 dtv v /\ val_wf dtv v /\
       intcall_expr_cont fp ce env es sa t ee sb u /\
       MAP FDOM es.scopes = MAP FDOM ee.scopes)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `expr_type e = ty` by metis_tac[compileEnvTheory.type_widens_to_word] >>
  `post_value_type ce e = ty` by simp[] >>
  `lower_value compile_expr ce (expr_type e) e sa = (op,sb)` by
    (gvs[] >> simp[exprLoweringTheory.lower_value_def, compileEnvTheory.comp_bind_def]) >>
  `gas_admissible (vyperState$bind (eval_expr fp.jc_cx e)
     (read_result fp.jc_cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  dxrule intcall_forced_producer_from_value >>
  rewrite_tac[intcall_forced_producer_def] >> disch_then drule_all >>
  disch_tac >>
  irule gas_outcome_exec_conseq >> goal_assum (drule_at Any) >> simp[] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
    metis_tac[bop_marked_scopes_dom] >>
  `value_runtime_typed env (expr_type e) v` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gasSummaryTheory.gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` assume_tac) >>
     irule memory_rhs_read_annotation_typed >>
     qexistsl [`ce`, `fp.jc_cx`,
       `es with gas_obs := gas_explicit marks t.vs_gas_readings ++ []`,
       `mid with gas_obs := []`] >>
     fs[expr_body_pre_gas_obs, SF ETA_ss]) >>
  `env.type_defs = get_tenv fp.jc_cx` by
    fs[intcall_expr_res_def, exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `val_wf dtv v` by
    (irule (cj 1 valueEncodingTypingTheory.value_has_type_val_wf) >>
     gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def]) >>
  gvs[loweringPostsTheory.expr_val_rel_def]
QED
