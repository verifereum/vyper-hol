(* Paired compiler cuts for the target and value of Append. *)
Theory s1PrefixAppendCodeCuts
Ancestors
  bodyFullAppend bodyFullShared stmtSimAppendResolved gasShadowCompileStmtHelpers
  gasShadowCompileBase gasShadowState gasShadow fragExec exprLoweringProps
  stmtLowering exprLowering compileEnv vyperAST

Theorem append_prefix_code_cuts:
  stmt_env cenv lctx ret_ty (Append t e) sa = (ce,sb) /\
  stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (Append t e))
    shadow_sa = (gas_shadow_env T ce,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ce = cenv /\
  ?r sp shadow_sp.
    compile_get_target_ptr compile_expr cenv t sa = (r,sp) /\
    compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
      (gas_shadow_target t) shadow_sa = (r,shadow_sp) /\
    gas_shadow_state sp shadow_sp /\
    ci_mono sa sp /\ ci_mono shadow_sa shadow_sp /\
    ci_mono sp sb /\ ci_mono shadow_sp shadow_sb /\
    fn_has_code sa sp func /\ fn_has_code shadow_sa shadow_sp shadow_func /\
    fn_has_code sp sb func /\ fn_has_code shadow_sp shadow_sb shadow_func /\
    (!b loc elem cap. r = (b,SOME loc,SOME (ValPT (ArrayT elem (Dynamic cap)))) ==>
      ?op sm shadow_sm.
        lower_value compile_expr cenv elem e sp = (op,sm) /\
        lower_value compile_expr (gas_shadow_env T cenv) elem (gas_shadow_expr e)
          shadow_sp = (op,shadow_sm) /\
        gas_shadow_state sm shadow_sm /\
        ci_mono sp sm /\ ci_mono shadow_sp shadow_sm /\
        ci_mono sm sb /\ ci_mono shadow_sm shadow_sb /\
        fn_has_code sp sm func /\ fn_has_code shadow_sp shadow_sm shadow_func /\
        fn_has_code sm sb func /\ fn_has_code shadow_sm shadow_sb shadow_func)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac append_resolved_target_prefix >>
  qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _`
    (assume_tac o REWRITE_RULE [gas_shadow_stmt_def]) >>
  qpat_assum `stmt_env _ _ _ (Append (gas_shadow_target _) _) _ = _`
    (mp_then (Pos hd) mp_tac append_resolved_target_prefix) >>
  disch_then (drule_then strip_assume_tac) >>
  rename1 `compile_get_target_ptr compile_expr cenv t sa = (r,sp)` >>
  rename1 `compile_get_target_ptr _ _ (gas_shadow_target t) shadow_sa = (sr,shadow_sp)` >>
  `sr = r /\ gas_shadow_state sp shadow_sp` by
    (irule gas_shadow_step >>
     qpat_assum `compile_get_target_ptr _ _ t sa = _` (irule_at Any) >>
     qpat_assum `compile_get_target_ptr _ _ (gas_shadow_target t) shadow_sa = _`
       (irule_at Any) >>
     simp[gas_shadow_stmt_get_target_ptr_env]) >>
  qpat_x_assum `ce = cenv` SUBST_ALL_TAC >>
  qpat_x_assum `sr = r` SUBST_ALL_TAC >>
  conj_tac >- REFL_TAC >>
  qexistsl_tac [`r`,`sp`,`shadow_sp`] >> simp[] >>
  rpt gen_tac >> disch_then SUBST_ALL_TAC >>
  qpat_assum `stmt_env cenv _ _ (Append t e) sa = _`
    (mp_then (Pos hd) mp_tac append_resolved_rhs_code_full) >>
  disch_then (drule_all_then strip_assume_tac) >>
  qpat_assum `stmt_env _ _ _ (Append (gas_shadow_target _) _) _ = _`
    (mp_then (Pos hd) mp_tac append_resolved_rhs_code_full) >>
  disch_then (drule_all_then strip_assume_tac) >>
  rename1 `lower_value _ cenv _ e sp = (vop,sm)` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) shadow_sp = (svop,shadow_sm)` >>
  `svop = vop /\ gas_shadow_state sm shadow_sm` by
    (irule gas_shadow_step >>
     qpat_assum `lower_value _ _ _ e sp = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr e) shadow_sp = _` (irule_at Any) >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  gvs[] >> qexistsl_tac [`vop`,`sm`,`shadow_sm`] >> simp[]
QED
