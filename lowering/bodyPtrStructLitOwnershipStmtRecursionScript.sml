Theory bodyPtrStructLitOwnershipStmtRecursion
Ancestors bodyPtrStructLitOwnershipStmtCases bodyPtrStructLitOwnershipStmtLoops
  bodyPtrStructLitOwnershipShape stmtLowering loweringShapeProps
  bodyPtrStructLitOwnershipRecursion
  bodyPtrStructLitCompilerOwnership loweringShapeDefs supportedExprTraverse
  bodyPtrStructLitOwnershipEnvironment bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipFreshness loweringShapeRules supportedStmtTraverse compileEnv list bodyPtrStructLitOwnershipPrimitives bodyPtrStructLitOwnershipLoops

Theorem alloc_run_stmt_shape_fresh[local]:
  ~supported_stmt_expr_exists expr_shape_root stmt /\ loop_ctx_shape_ok lc /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_stmt ce lc ty stmt) (\u s. T) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_stmt ce lc ty stmt) (\u s. fresh_outputs s)
Proof
  strip_tac >> irule alloc_run_conseq >> irule_at Any alloc_run_shape_join >>
  irule_at Any (cj 1 compile_stmt_shape) >>
  goal_assum (drule_at Any) >>
  simp[shape_state_def, shape_base_fresh_outputs]
QED

Theorem alloc_run_compile_stmt_route_mutual:
  (!ce lc ty stmt.
    ce.ce_alloca_locals /\ loop_ctx_shape_ok lc /\
    ~supported_stmt_expr_exists expr_shape_root stmt ==>
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (comp_bind (declare_stmt_local ce stmt) (\env. compile_stmt env lc ty stmt))
      (\u s. fresh_outputs s)) /\
  (!ce lc ty stmts.
    ce.ce_alloca_locals /\ loop_ctx_shape_ok lc /\
    ~supported_stmts_expr_exists expr_shape_root stmts ==>
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (compile_stmts ce lc ty stmts) (\u s. fresh_outputs s))
Proof
  ho_match_mp_tac compile_stmt_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[supported_stmt_expr_exists_def,
    supported_assert_exists_def, supported_raise_exists_def,
    supported_iterator_exists_def, supported_expr_exists_def] >> rpt strip_tac >>
  FIRST [
    (irule alloc_run_stmt_annassign_route >> simp[] >> NO_TAC),
    (rename1 `compile_stmts _ _ _ (_::_)` >> suspend "cons"),
    (rename1 `compile_stmts _ _ _ []` >>
      simp[Once compile_stmt_def, comp_return_def, alloc_run_def,
        alloc_frame_refl, shape_state_def, shape_base_fresh_outputs] >> NO_TAC),
    (irule alloc_run_stmt_nonannassign_route >> conj_tac >- simp[] >>
      FIRST [
        (rename1 `compile_stmt _ _ _ (If _ _ _)` >> suspend "if"),
        (rename1 `compile_stmt _ _ _ (For _ _ (Range _ _) _ _)` >> suspend "range"),
        (rename1 `compile_stmt _ _ _ (For _ _ (Array _) _ _)` >> suspend "array"),
        (gvs[supported_assignment_exists_def] >>
         FIRST [
           (simp[alloc_run_stmt_assert_simple, alloc_run_stmt_return_some,
             alloc_run_stmt_raise_reason, alloc_run_stmt_assert_reason,
             alloc_run_stmt_append, alloc_run_stmt_augassign,
             alloc_run_stmt_assign_base] >> NO_TAC),
           (irule alloc_run_stmt_log >>
             gvs[supported_exprs_exists_every, EVERY_MEM] >> NO_TAC),
           (irule alloc_run_conseq >>
             FIRST [irule_at Any alloc_run_stmt_return_none,
               irule_at Any alloc_run_stmt_assign_tuple,
               irule_at Any (cj 1 alloc_run_stmt_loop_exit),
               irule_at Any (cj 2 alloc_run_stmt_loop_exit),
               irule_at Any (cj 1 alloc_run_stmt_raise_simple),
               irule_at Any (cj 2 alloc_run_stmt_raise_simple)] >>
             simp[shape_state_def, shape_base_fresh_outputs] >> NO_TAC),
           (irule alloc_run_stmt_shape_fresh >>
             simp[supported_stmt_expr_exists_def, supported_assert_exists_def,
               supported_raise_exists_def] >>
             FIRST [
               (irule alloc_run_stmt_expr >> simp[] >> NO_TAC),
               (irule alloc_run_conseq >> irule_at Any alloc_run_stmt_pass >> simp[] >> NO_TAC),
               (simp[Once compile_stmt_def, comp_ignore_bind_def] >>
                 irule alloc_run_bind >> qexists `\u s. fresh_outputs s` >>
                 reverse conj_tac
                 >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_empty_fresh >>
                     simp[shape_state_def, shape_base_fresh_outputs]) >>
                 simp[comp_return_def, alloc_run_def, alloc_frame_refl] >> NO_TAC)]) ])]) ]
QED

Resume alloc_run_compile_stmt_route_mutual[if]:
  irule alloc_run_stmt_shape_fresh >> simp[supported_stmt_expr_exists_def] >>
  gvs[] >> irule (Q.INST [`internal` |-> `IS_SOME ce.ce_return_pc`] alloc_run_compile_stmt_if) >>
  simp[bodyPtrStructLitOwnershipRecursionTheory.alloc_run_compile_expr,
    cj 1 compile_expr_shape] >> rpt conj_tac >>
  FIRST [
    (irule shape_step_conseq >> irule_at Any (cj 2 compile_stmt_shape) >>
      simp[] >> NO_TAC),
    (irule alloc_run_conseq >> goal_assum (drule_at Any) >> simp[] >> NO_TAC) ]
QED
Resume alloc_run_compile_stmt_route_mutual[range]:
  irule alloc_run_stmt_shape_fresh >>
  simp[supported_stmt_expr_exists_def, supported_iterator_exists_def] >>
  irule (Q.INST [`internal` |-> `IS_SOME ce.ce_return_pc`]
    alloc_run_compile_stmt_range) >>
  simp[alloc_run_compile_expr, cj 1 compile_expr_shape] >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (qpat_x_assum `env.ce_return_pc = _`
        (fn th => rewrite_tac[GSYM th]) >>
      irule shape_step_conseq >> irule_at Any (cj 2 compile_stmt_shape) >>
      simp[loop_ctx_shape_ok_def, jump_label_ok_def]) >>
  irule alloc_run_conseq >> first_x_assum (irule_at Any) >>
  simp[loop_ctx_shape_ok_def, jump_label_ok_def]
QED
Resume alloc_run_compile_stmt_route_mutual[array]:
  irule alloc_run_stmt_shape_fresh >>
  simp[supported_stmt_expr_exists_def, supported_iterator_exists_def] >>
  irule (Q.INST [`internal` |-> `IS_SOME ce.ce_return_pc`]
    alloc_run_compile_stmt_array) >>
  simp[alloc_run_compile_expr, cj 1 compile_expr_shape] >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (qpat_x_assum `env.ce_return_pc = _`
        (fn th => rewrite_tac[GSYM th]) >>
      irule shape_step_conseq >> irule_at Any (cj 2 compile_stmt_shape) >>
      simp[loop_ctx_shape_ok_def, jump_label_ok_def]) >>
  irule alloc_run_conseq >> first_x_assum (irule_at Any) >>
  simp[loop_ctx_shape_ok_def, jump_label_ok_def]
QED

Resume alloc_run_compile_stmt_route_mutual[cons]:
  rewrite_tac[alloc_run_def] >>
  map_every qx_gen_tac [`s`, `u`, `s2`] >> strip_tac >>
  qpat_x_assum `compile_stmts _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, comp_get_def, comp_bind_def] >>
  Cases_on `block_is_terminated s`
  >- (simp[comp_return_def] >> strip_tac >>
      gvs[alloc_frame_refl, shape_state_def, shape_base_fresh_outputs]) >>
  simp[] >>
  Cases_on `declare_stmt_local ce stmt s` >> rename1 `_ = (env,sd)` >>
  Cases_on `compile_stmt env lc ty stmt sd` >> rename1 `_ = (uu,sh)` >>
  simp[comp_bind_def, comp_ignore_bind_def] >> strip_tac >>
  qpat_assum `!cs ce. _ ==> _ ==> alloc_run _ (comp_bind _ _) _`
    (qspecl_then [`s`, `ce`] mp_tac) >> simp[] >>
  disch_then (mp_tac o SRULE [alloc_run_def]) >>
  disch_then (qspecl_then [`s`, `sh`] mp_tac) >>
  simp[comp_bind_def] >> strip_tac >> suspend "cons_shape"
QED
Resume alloc_run_compile_stmt_route_mutual[cons_shape]:
  gvs[] >>
  mp_tac (Q.SPECL [`F`, `ce`, `stmt`] declare_stmt_local_shape) >>
  rewrite_tac[shape_step_def] >>
  disch_then (qspecl_then [`s`, `env`, `sd`] mp_tac) >> simp[] >> strip_tac >>
  drule declare_stmt_local_alloca_mode >> strip_tac >>
  mp_tac (Q.SPECL [`env`, `lc`, `ty`, `stmt`] (cj 1 compile_stmt_shape)) >>
  simp[shape_step_def] >>
  disch_then (qspecl_then [`sd`, `sh`] mp_tac) >> simp[] >> strip_tac >>
  `cenv_shape_ok sh env` by
    (mp_tac cenv_shape_ok_stable >> simp[shape_stable_def] >>
     disch_then drule >> disch_then drule >> simp[]) >>
  qpat_assum `!cs ce. _ ==> _ ==> alloc_run _ (compile_stmts _ _ _ _) _`
    (qspecl_then [`s`, `env`] mp_tac) >> simp[] >>
  disch_then (mp_tac o SRULE [alloc_run_def]) >>
  disch_then (qspecl_then [`sh`, `s2`] mp_tac) >> simp[] >>
  metis_tac[alloc_frame_trans]
QED
Finalise alloc_run_compile_stmt_route_mutual
