Theory bodyImmutableAugAssignCompose
Ancestors
  bodyImmutableAugAssignFacts bodyImmutableAugAssignPaths bodyImmutableAugAssignExec
  stmtSimAugAssignStorage stmtSimAugAssignAttr stmtSimAugAssignPlace
  bodySim exprSimHypsDefs exprSimHyps stmtSimDefs stmtSimProps
  stmtLowering exprLowering exprLoweringProps compileEnv loweringPosts
  freshWrites emitHelperProps localPtrsProps finite_map fragExec venomState
  exprSimDefs gasContext gasSummary gasOutcome fragGasMode fragGasPath
  stmtSimAugAssign vyperTypeInvariants vyperTypeSystem
  exprSimSource exprSimProps exprBopSimProps exprBopSimDefs exprOperandVar
  vyperInterpreter vyperState

Theorem immutable_deploy_augassign_frag:
  !ctx func cx lctx RetQ cenv ret_ty env env' tops nsid ty bop e es ity.
    body_inv tops ctx cenv cx /\ cx.in_deploy /\
    supported_immutable_type tops nsid = SOME ity /\
    type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget nsid) bop e) =
      SOME env' /\
    ((?s p s1 s2 cur s3 s4 ptv s5.
        eval_target_place cx (TopLevelNameTarget nsid) s = (INL p,s1) /\
        read_place cx p s2 = (INL cur,s3) /\
        place_type_value cx p s4 = (INL ptv,s5)) ==>
     expr_sim_case F ctx func cenv cx e) /\
    expr_body_pre cenv cx env e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty (TopLevelNameTarget nsid) bop e))
      (eval_stmt cx (AugAssign ty (TopLevelNameTarget nsid) bop e)) es
Proof
  rpt gen_tac >> strip_tac >> PairCases_on `nsid` >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all immutable_augassign_metadata >> strip_tac >> gvs[] >>
  drule_all immutable_augassign_entry >> strip_tac >>
  drule_all immutable_augassign_source_prefix >> strip_tac >>
  `expr_sim_case F ctx func cenv cx e` by metis_tac[] >>
  drule_all immutable_augassign_prefix_obs >> strip_tac >>
  drule aug_place_typing >> strip_tac >>
  simp[stmt_frag_def,stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_all immutable_augassign_code_parts >> strip_tac >> gvs[] >>
  suspend "load_prefix"
QED

Resume immutable_deploy_augassign_frag[load_prefix]:
  `cs_extends sa s1` by
    metis_tac[cs_appends_emit_helpers,cs_appends_def] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_binop_grows >> strip_tac >>
  `cs_extends s3 sb` by
    metis_tac[cs_appends_emit_helpers,cs_appends_def] >>
  `cs_extends s1 s3 /\ cs_extends s1 sb /\ cs_extends s2 sb /\
   cs_extends sa s2 /\ cs_extends sa s3` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    metis_tac[fn_has_code_mid,cs_extends_refl] >>
  `off < dimword (:256)` by decide_tac >>
  `mload off s0 = typed_val_to_w256 tv v` by
    (irule immutable_augassign_load >> simp[] >> metis_tac[]) >>
  drule_all immutable_augassign_load_frame >> strip_tac >>
  rename1 `value_has_type tv v0` >>
  suspend "rhs_outcome"
QED

Resume immutable_deploy_augassign_frag[rhs_outcome]:
  `expr_sim ctx func cenv cx ity e (es with gas_obs := [])` by
    (irule expr_sim_case_apply >> simp[] >> conj_tac
     >- (qexists_tac `env` >> simp[]) >>
     qexists_tac `F` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok
    (es with gas_obs := [])` by
    (simp[] >> irule immutable_augassign_rhs_admissible >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) t` by simp[] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`s1`,`s2`,`rhs_op`,`t`] mp_tac) >>
  impl_tac >- simp[] >>
  simp[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- suspend "rhs_summary" >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  irule immutable_augassign_rhs_exempt >> conj_tac
  >- metis_tac[] >> qexists_tac `t` >> simp[]
QED

Resume immutable_deploy_augassign_frag[rhs_summary]:
  qexists_tac `marks` >> disj1_tac >>
  qpat_x_assum `gasSummary$gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >> strip_tac
  >- suspend "rhs_normal" >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
  qexistsl_tac [`INR ex`,`es_end`,`r`] >> conj_tac
  >- (irule immutable_augassign_rhs_exception_exec >> conj_tac
      >- metis_tac[] >> qexists_tac `t` >> simp[]) >>
  disj2_tac >> simp[] >> gen_tac >> simp[stmt_exit_def] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

Resume immutable_deploy_augassign_frag[rhs_normal]:
  gvs[] >>
  rename1 `expr_post ctx func cenv cx e _ s1 s2 t (ee with gas_obs := []) v rhs_op u` >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks t.vs_gas_readings) =
      (INL v,ee with gas_obs := [])` by
    (drule gas_marked_exec_observation >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  `well_formed_type (get_tenv cx) ity` by
    (fs[expr_sim_inv_def,env_consistent_def,env_context_consistent_def] >>
     metis_tac[assignable_type_well_formed]) >>
  drule_all augassign_attr_binop_ready >>
  disch_then (qspecl_then [`func`,`ee with gas_obs := []`,`ctx`] strip_assume_tac) >>
  `expr_res_ok (bop_result cx ity bop [ity;expr_type e] v0 v ee)` by
    (`expr_res_ok (bop_result cx ity bop [ity;expr_type e] v0 v
       (ee with gas_obs := []))` suffices_by simp[] >>
     irule immutable_augassign_binop_admissible >> metis_tac[]) >>
  suspend "binop_ready"
QED

Resume immutable_deploy_augassign_frag[binop_ready]:
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks t.vs_gas_readings)` by simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_result) >>
  strip_tac >> gvs[] >>
  `word_value v0` by metis_tac[exprSimSourceTheory.word_value_type_typed] >>
  `eval_operand (Var out) t = SOME (val_to_w256 v0)` by
    simp[typed_val_to_w256_word_value] >>
  `eval_operand rhs_op u = SOME (val_to_w256 v)` by
    (irule expr_val_rel_word >> fs[expr_post_def] >>
     goal_assum (drule_at Any) >> simp[exprSimSourceTheory.word_value_type_word]) >>
  `eval_operand (Var out) u = SOME (val_to_w256 v0)` by
    (irule eval_operand_frame >> simp[] >>
     qexistsl_tac [`s1`,`t`] >> gvs[expr_post_def]) >>
  `not_fresh_at s2 out /\ local_ptrs_reserved cenv s2` by
    metis_tac[not_fresh_at_mono,local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) u` by
    fs[expr_post_def] >>
  `~u.vs_halted` by
    metis_tac[gas_marked_exec_def,gas_marked_path_exec,gas_path_normal] >>
  qpat_x_assum `binop_frag _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [exprBopSimDefsTheory.binop_frag_def,
                           exprBopSimDefsTheory.binop_frag_words_def]) >>
  disch_then (qspecl_then [`s2`,`s3`,`Var out`,`rhs_op`,`res_op`,`u`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[exprOperandVarTheory.compile_lower_value_var]) >>
  strip_tac >- suspend "operator_normal" >> suspend "operator_exit"
QED

Resume immutable_deploy_augassign_frag[operator_normal]:
  gvs[] >> rename1 `eval_operand res_op s = SOME (val_to_w256 result)` >>
  `bop_result cx ity bop [ity;expr_type e] v0 v ee =
     case evaluate_binop
       (case type_to_int_bound ity of SOME bound => bound | NONE => Unsigned 0)
       tv bop v0 v of INL x => INL x | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  `evaluate_binop
     (case type_to_int_bound ity of SOME bound => bound | NONE => Unsigned 0)
     tv bop v0 v = INL result` by gvs[AllCaseEqs()] >>
  `value_has_type tv result` by simp[] >>
  `eval_operand res_op s = SOME (typed_val_to_w256 tv result)` by
    simp[typed_val_to_w256_word_value] >>
  `?fin last. write_place cx (ImmutablePlace cenv.ce_module nsid1 []) result
      (ee with gas_obs := []) = (INL (),fin) /\
    gas_marked_path F ctx func s 0 (OK last) /\
    stmt_post ctx func cx lctx cenv cenv s3 sb s (INL ()) fin last` by
    (irule immutable_augassign_store_post_path >> simp[] >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`env`,`res_op`,`s3`] >> simp[]) >>
  suspend "store_post"
QED

Resume immutable_deploy_augassign_frag[store_post]:
  `stmt_post ctx func cx lctx cenv cenv s2 sb u (INL ()) fin last` by
    (irule stmtSimDeclComposeTheory.stmt_post_entry_frame >>
     qexistsl_tac [`s`,`s3`] >> simp[] >> metis_tac[not_fresh_at_mono]) >>
  `stmt_post ctx func cx lctx cenv cenv s1 sb t (INL ()) fin last` by
    (irule stmt_post_expr_entry_frame >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `stmt_post ctx func cx lctx cenv cenv sa sb s0 (INL ()) fin last` by
    (irule stmtSimDeclComposeTheory.stmt_post_entry_frame >>
     qexistsl_tac [`t`,`s1`] >> simp[] >>
     rpt strip_tac >> irule not_fresh_at_mono >>
     qexists_tac `sa` >> simp[] >>
     qspecl_then [`MLOAD`,`[Lit (n2w off)]`,`sa`] mp_tac ci_mono_emit_op >>
     simp[ci_mono_def]) >>
  `gas_marked_path F ctx func u 0 (OK last)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `fin = fin with gas_obs := []` by
    (drule immutable_write_place_gas_obs >>
     disch_then (qspec_then `[]` mp_tac) >> simp[] >> strip_tac >> gvs[]) >>
  qexistsl_tac [`INL ()`,`fin`,`OK last`] >> simp[] >>
  reverse conj_tac >- (disj1_tac >> metis_tac[]) >>
  irule immutable_augassign_rhs_normal_exec >>
  qexistsl_tac [`ee`,`ImmutablePlace NONE nsid1 []`,`t`,`tv`,`u`,`v`,`v0`] >>
  simp[] >> irule immutable_augassign_continuation_exec >>
  simp[lift_sum_def,bind_def,return_def] >>
  qpat_x_assum `write_place _ _ _ _ = _` mp_tac >> simp[]
QED

Resume immutable_deploy_augassign_frag[operator_exit]:
  `bop_result cx ity bop [ity;expr_type e] v0 v ee =
     case evaluate_binop
       (case type_to_int_bound ity of SOME bound => bound | NONE => Unsigned 0)
       tv bop v0 v of
       INL x => INL x | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  Cases_on `evaluate_binop
       (case type_to_int_bound ity of SOME bound => bound | NONE => Unsigned 0)
       tv bop v0 v`
  >- (gvs[] >> fs[expr_exit_def,exit_result_def]) >>
  gvs[] >>
  qexistsl_tac [`INR (Error y)`,`ee with gas_obs := []`,`r`] >>
  conj_tac
  >- (irule immutable_augassign_rhs_normal_exec >>
      qexistsl_tac [`ee`,`ImmutablePlace NONE nsid1 []`,`t`,`tv`,`u`,`v`,`v0`] >>
      simp[] >> irule immutable_augassign_continuation_exec >>
      simp[lift_sum_def,bind_def,raise_def]) >>
  disj2_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]
QED

Finalise immutable_deploy_augassign_frag
