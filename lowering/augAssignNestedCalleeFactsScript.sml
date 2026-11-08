(* Finite callee boundaries independent of bodyAugAssignOther. *)
Theory augAssignNestedCalleeFacts
Ancestors
  augAssignNestedReachProbe bodyAssignPlace bodyExprPreFacts
  bodySimExprCases stmtSimSeqEnv

Theorem nested_replacement_expr_ok:
  !cx. body_expr_ok cx nested_reach_replacement
Proof
  gen_tac >>
  rewrite_tac[nested_reach_replacement_def] >>
  irule body_make_array_case >>
  simp[bodySimTheory.body_exprs_ok_def] >> strip_tac >>
  irule body_make_array_case >>
  simp[bodySimTheory.body_exprs_ok_def]
QED

Theorem nested_replacement_stmt_ok:
  !cx. body_stmt_ok cx
    (Assign (BaseTarget (TopLevelNameTarget (NONE,"a"))) nested_reach_replacement)
Proof
  rw[bodySimTheory.body_stmt_ok_def] >>
  irule body_assign_place_case >>
  simp[bodySimTheory.body_base_target_ok_def, nested_replacement_expr_ok] >>
  fs[nested_reach_replacement_def, exprLoweringTheory.lowered_value_type_def] >>
  metis_tac[]
QED

Theorem nested_replacement_body_ok:
  !cx. body_stmts_ok cx nested_reach_body
Proof
  rewrite_tac[nested_reach_body_def, bodySimTheory.body_stmts_ok_def] >>
  rpt gen_tac >> strip_tac >>
  fs[supportedStmtsTheory.supported_stmt_def,
     vyperTypeSystemTheory.type_stmt_def,
     supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
     vyperTypeCallGraphTheory.int_calls_stmt_def, AllCaseEqs()] >>
  irule stmt_frag_cons_env >>
  simp[cj 1 stmtLoweringMonoTheory.compile_stmt_cs_mono, stmts_env_cs_mono] >>
  reverse conj_tac
  >- (irule (REWRITE_RULE [bodySimTheory.body_stmt_ok_def] nested_replacement_stmt_ok) >>
      fs[supportedStmtsTheory.supported_stmt_def,
         vyperTypeSystemTheory.type_stmt_def,
         supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
         vyperTypeCallGraphTheory.int_calls_stmt_def] >>
      metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left]) >>
  rpt strip_tac >>
  gvs[] >>
  `same_frame cenv c` by metis_tac[bodySimTheory.cenv_top_ext_same_frame] >>
  `expr_sim_inv c cx env es1` by
    (drule_at (Pat `eval_stmt _ _ _ = _`) expr_sim_inv_stmt >>
     disch_then (qspecl_then [`tops`, `bindings`] mp_tac) >>
     disch_then (drule_at (Pat `stmt_env _ _ _ _ _ = _`)) >>
     simp[supportedStmtsTheory.supported_stmt_def,
          vyperTypeSystemTheory.type_stmt_def,
          vyperTypeCallGraphTheory.int_calls_stmt_def,
          exprSimHypsDefsTheory.expr_sim_inv_gas_obs] >>
     fs[bodySimTheory.body_inv_def] >>
     metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left]) >>
  irule stmt_frag_cons_env >>
  simp[cj 1 stmtLoweringMonoTheory.compile_stmt_cs_mono, stmts_env_cs_mono,
       stmtSimZeroTheory.stmt_frag_nil] >>
  `stmt_exprs_ok c (Return (SOME (Literal (BaseT (UintT 256)) (IntL 0))))` by
    metis_tac[stmt_exprs_ok_same_frame] >>
  `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
  `expr_body_pre c cx env (Literal (BaseT (UintT 256)) (IntL 0)) es1` by
    (irule stmt_expr_body_pre >>
     simp[supportedExprTraverseTheory.supported_expr_exists_def,
          vyperTypeCallGraphTheory.int_calls_expr_def] >>
     `cx_tops cx = tops` by
       (irule gasContextTheory.cx_tops_module >> fs[bodySimTheory.body_inv_def]) >>
     `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
        is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target)` by
       fs[bodySimTheory.body_inv_def] >>
     fs[bodySimTheory.stmt_exprs_ok_def,
        supportedProgramTheory.expr_abi_decode_target_root_def,
        supportedExprTraverseTheory.expr_has_evm_run_def,
        supportedExprTraverseTheory.expr_evm_run_root_def,
        exprLoweringTheory.is_extcode_def,
        supportedStmtTraverseTheory.supported_stmt_expr_exists_def,
        supportedExprTraverseTheory.supported_expr_exists_def] >>
     qexists_tac `[]` >>
     irule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_mono >>
     goal_assum (drule_at Any) >> simp[]) >>
  fs[bodySimTheory.frame_ret_ok_def] >>
  first_x_assum irule >>
  simp[vyperTypeSystemTheory.type_stmt_def,
       vyperTypeCallGraphTheory.int_calls_stmt_def,
       vyperTypeCallGraphTheory.int_calls_expr_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `body_expr_ok cx (Literal (BaseT (UintT 256)) (IntL 0))` by
    (irule body_expr_ok_intro >>
     simp[vyperTypeCallGraphTheory.int_calls_expr_def]) >>
  fs[bodySimTheory.body_expr_ok_def] >- metis_tac[] >>
  conj_tac
  >- (irule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_mono >>
      goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `env` >> simp[]
QED
