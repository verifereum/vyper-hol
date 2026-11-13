(* Return composition parameterized by its terminal continuation. *)
Theory bodyIntCallReturnUnlockCompose
Ancestors
  bodyIntCallJointContract bodyIntCallJointStmtSeq bodyIntCallFamStmtReturnTypes
  bodyIntCallFamStmtReturnCompose bodyIntCallFamStmtReturnEndpointTypes
  bodyExprPreFacts exprSimHypsDefs exprSimDefs exprSimHyps exprSimSource
  stmtSimDefs stmtSimProps stmtSimReturn stmtSimReturnWiden
  stmtLowering stmtLoweringMono exprLowering exprLoweringProps compileEnv loweringPosts
  fragExec vyperInterpreter vyperState vyperTypeSystem vyperTypeCallStackSoundness
  supportedStmts supportedStmtTraverse supportedExprTraverse supportedExprs
  allocLimits gasOutcome gasSummary gasSummaryCompose fragGasMode bodySim
  vyperTypeCallGraph gasContext

Theorem intcall_valued_return_from_endpoint:
  intcall_forced_producer fp e /\
  (!ce env ee sm t es tv v op sa sb.
    intcall_frame_ok fp /\ intcall_joint_res fp ce env ee sm t /\
    body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
    expr_body_pre ce fp.jc_cx env e es /\
    type_widens_to env.type_defs (expr_type e) fp.jc_ret_ty /\
    fp.jc_ret_ty <> NoneT /\
    evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME tv /\
    value_has_type tv v /\ value_has_type fp.jc_ret_tv v /\
    expr_val_rel fp.jc_cx (post_value_type ce e) v op t /\
    expr_val_at ce fp.jc_cx (post_value_type ce e) sa sm ee v op t /\
    (!x. op = Var x ==> not_fresh_at sm x) /\
    (post_value_type ce e <> NoneT /\ ~is_word_type (post_value_type ce e) /\
     ~is_bytestring_type (post_value_type ce e) ==>
     !tv'. evaluate_type (get_tenv fp.jc_cx) (post_value_type ce e) = SOME tv' ==>
      ?w a k. eval_operand op t = SOME w /\ a <= w2n w /\
       w2n w + type_memory_size tv' <= a+k /\ a+k < dimword (:256) /\
       (fp.jc_lo <= a \/ ?b z. fp.jc_staged b z /\ b <= a /\ a+k <= b+z)) /\
    compile_internal_return_from_env ce fp.jc_ret_ty (lowered_value_type ce e)
      op fp.jc_rpc sm = ((),sb) /\
    fn_has_code sm sb fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?k r. gas_path fp.jc_ctx fp.jc_func t k r /\ exit_result r /\
      intcall_stmt_exit fp (INR (ReturnException v)) ee r) ==>
  intcall_stmts_producer fp [Return (SOME e)]
Proof
  strip_tac >>
  simp[intcall_stmts_producer_def, eval_stmts_singleton] >>
  rpt gen_tac >> strip_tac >>
  gvs[supported_stmt_def, type_stmt_def, int_calls_stmt_def,
      supported_stmt_expr_exists_def, AllCaseEqs()] >>
  `ce.ce_return_pc = SOME (PtrVar fp.jc_rpc 0)` by
    fs[intcall_frame_ok_def, intcall_joint_res_def, intcall_expr_res_def,
       same_frame_def, compile_env_component_equality] >>
  qpat_x_assum `stmts_env _ _ _ _ _ = _` mp_tac >>
  simp[stmts_env_singleton, stmt_env_def, declare_stmt_local_def,
       compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `lower_value compile_expr ce fp.jc_ret_ty e sa` >>
  rename1 `_ = (op,sm)` >> simp[] >> strip_tac >> gvs[] >>
  `expr_body_pre ce fp.jc_cx env e es` by suspend "exprpre" >>
  `compile_internal_return_from_env ce fp.jc_ret_ty (lowered_value_type ce e)
      op fp.jc_rpc sm = ((),sb) /\ ce' = ce` by
    (Cases_on `compile_internal_return_from_env ce fp.jc_ret_ty
       (lowered_value_type ce e) op fp.jc_rpc sm` >> gvs[]) >>
  `ci_mono sa sm /\ ci_mono sm sb` by
    (mp_tac (cj 2 ci_mono_compile_expr_sa) >>
     mp_tac (cj 2 ci_mono_return_helpers) >> metis_tac[pairTheory.SND]) >>
  `fn_has_code sa sm fp.jc_func /\ fn_has_code sm sb fp.jc_func` by
    (irule fn_has_code_split >>
     fs[ci_mono_def] >> goal_assum (drule_at Any)) >>
  `gas_admissible (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
     expr_res_ok es` by metis_tac[return_forced_admissible] >>
  `intcall_expr_res fp ce env es sa s` by fs[intcall_joint_res_def] >>
  qpat_x_assum `intcall_forced_producer _ _`
    (mp_tac o REWRITE_RULE [intcall_forced_producer_def]) >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac [gas_outcome_def, gas_summary_at_def] >>
  strip_tac
  >- (gvs[] >> suspend "normal")
  >- suspend "exceptional" >>
  suspend "exempt"
QED

Resume intcall_valued_return_from_endpoint[exprpre]:
  `~supported_expr_exists
    (\e'. ~is_extcode e' /\ (~byte_widths_expr e' \/ ~alloc_limits_expr ce e')) e` by
   (`~supported_stmt_expr_exists (\e. ~is_extcode e /\ ~alloc_limits_expr ce e)
       (Return (SOME e))` by
      (irule allocLimitsPropsTheory.alloc_limits_stmt_exists >>
       fs[intcall_joint_res_def, intcall_expr_res_def, stmt_exprs_ok_def]) >>
    `(\e'. ~is_extcode e' /\ (~byte_widths_expr e' \/ ~alloc_limits_expr ce e')) =
     (\e'. (\x. ~is_extcode x /\ ~byte_widths_expr x) e' \/
            (\x. ~is_extcode x /\ ~alloc_limits_expr ce x) e')` by
      (simp[FUN_EQ_THM] >> metis_tac[]) >>
    pop_assum SUBST1_TAC >>
    rewrite_tac[supported_expr_exists_disj] >>
    fs[intcall_joint_res_def, intcall_expr_res_def, stmt_exprs_ok_def,
       supported_stmt_expr_exists_def, supported_expr_exists_def]) >>
  irule stmt_expr_body_pre >>
  fs[intcall_joint_res_def, intcall_expr_res_def, stmt_exprs_ok_def,
     supported_stmt_expr_exists_def, alloc_limits_stmt_def,
     supported_expr_exists_def] >>
  drule supported_expr_body_calls >> strip_tac >>
  fs[body_inv_def, cx_tops_def, AllCaseEqs()] >>
  qexists_tac `[]` >> simp[call_evaluation_safe_def] >>
  fs[intcall_frame_ok_def] >> metis_tac[]
QED

Resume intcall_valued_return_from_endpoint[exceptional]:
  `?exc. res = INR exc` by
    (Cases_on `res` >> fs[expr_exit_def]) >> gvs[] >>
  `gas_marked_exec F (fp.jc_ctx,fp.jc_func)
     (eval_stmt fp.jc_cx (Return (SOME e))) (es,s) marks (INR exc) es_end r` by
    (fs[gas_marked_exec_def] >>
     simp[gas_marked_exec_def] >> gen_tac >>
     first_x_assum (qspec_then `tail` mp_tac) >>
     simp[eval_return_forced, bind_def] >>
     Cases_on `eval_expr fp.jc_cx e
       (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail)` >>
     rename1 `_ = (raw,mid)` >> Cases_on `raw` >> simp[] >>
     rename1 `read_result fp.jc_cx rv mid` >>
     Cases_on `read_result fp.jc_cx rv mid` >>
     rename1 `_ = (forced,fin)` >> Cases_on `forced` >> simp[]) >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INR exc`, `es_end`, `r`] >>
  simp[] >> disj2_tac >> simp[intcall_stmt_exit_def] >>
  disj1_tac >> Cases_on `exc` >> Cases_on `r` >>
  fs[expr_exit_def] >> rename1 `Error err` >> Cases_on `err` >> fs[expr_exit_def]
QED

Resume intcall_valued_return_from_endpoint[exempt]:
  pure_rewrite_tac [gas_outcome_def] >>
  qexists_tac `marks` >> disj2_tac >>
  drule return_forced_exempt >> metis_tac[]
QED

Resume intcall_valued_return_from_endpoint[normal]:
  `?k r. gas_path fp.jc_ctx fp.jc_func t k r /\ exit_result r /\
     intcall_stmt_exit fp (INR (ReturnException v))
       (es_end with gas_obs := []) r` by suspend "terminal" >>
  drule_all forced_return_marked_exec >> strip_tac >>
  qexists_tac `marks ++ REPLICATE k F` >> disj1_tac >>
  qexistsl_tac [`INR (ReturnException v)`, `es_end`, `r`] >> simp[] >>
  disj2_tac >> simp[]
QED

Resume intcall_valued_return_from_endpoint[terminal]:
  `expr_sim_inv ce fp.jc_cx env es` by fs[expr_body_pre_def] >>
  drule_all return_post_type_widens >> strip_tac >>
  drule_all marked_forced_post_typed >> strip_tac >>
  `evaluate_type (get_tenv fp.jc_cx) fp.jc_ret_ty = SOME fp.jc_ret_tv` by
    fs[intcall_frame_ok_def] >>
  drule_all marked_forced_destination_typed >> strip_tac >>
  `intcall_joint_res fp ce env (es_end with gas_obs := []) sm t` by
    fs[intcall_joint_res_def, intcall_expr_cont_def] >>
  fs[intcall_expr_cont_def] >>
  first_x_assum irule >> simp[] >>
  goal_assum (drule_at (Pat `compile_internal_return_from_env _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> goal_assum (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  fs[intcall_expr_cont_def] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Finalise intcall_valued_return_from_endpoint
