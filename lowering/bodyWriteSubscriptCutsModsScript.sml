(* The real and shadow write-target compilers cut at the same operands. *)
Theory bodyWriteSubscriptCutsMods
Ancestors
  targetSubscriptContinuation gasShadowCompileStmtHelpers bodyFullShared
  gasShadow gasShadowState exprLoweringProps fragExec

(* ci_mono includes code extension and the next-variable/ID bounds for
   retaining operands allocated by either prefix. *)
Theorem write_subscript_paired_cuts_mods:
  compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa = (r,sb) /\
  compile_get_target_ptr compile_expr (gas_shadow_env sd cenv)
    (gas_shadow_target (SubscriptTarget bt e)) shadow_sa = (r,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  gas_shadow_state sb shadow_sb /\
  ?rb sm ix sn shadow_sm shadow_sn.
    compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
    lower_value compile_expr cenv (expr_type e) e sm = (ix,sn) /\
    target_subscript_suffix cenv e rb ix sn = (r,sb) /\
    compile_get_target_ptr compile_expr (gas_shadow_env sd cenv)
      (gas_shadow_target bt) shadow_sa = (rb,shadow_sm) /\
    lower_value compile_expr (gas_shadow_env sd cenv) (expr_type e)
      (gas_shadow_expr e) shadow_sm = (ix,shadow_sn) /\
    target_subscript_suffix (gas_shadow_env sd cenv) (gas_shadow_expr e)
      rb ix shadow_sn = (r,shadow_sb) /\
    gas_shadow_state sm shadow_sm /\ gas_shadow_state sn shadow_sn /\
    ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb /\
    ci_mono shadow_sa shadow_sm /\ ci_mono shadow_sm shadow_sn /\
    ci_mono shadow_sn shadow_sb /\
    fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func /\
    fn_has_code shadow_sa shadow_sm shadow_func /\
    fn_has_code shadow_sm shadow_sn shadow_func /\
    fn_has_code shadow_sn shadow_sb shadow_func
Proof
  strip_tac >> conj_tac
  >- (`r = r /\ gas_shadow_state sb shadow_sb` suffices_by simp[] >>
      irule gas_shadow_step >> rpt (first_assum (irule_at Any)) >>
      simp[gas_shadow_stmt_get_target_ptr_env]) >>
  qpat_assum `compile_get_target_ptr _ _ (SubscriptTarget bt e) sa = _`
    (strip_assume_tac o MATCH_MP target_subscript_compile_decompose) >>
  drule_all_then strip_assume_tac target_subscript_compile_intervals >>
  drule_all_then strip_assume_tac target_subscript_interval_code >>
  qpat_x_assum `compile_get_target_ptr _ _ (gas_shadow_target _) _ = _`
    (strip_assume_tac o SIMP_RULE bool_ss [gas_shadow_expr_type] o
     MATCH_MP target_subscript_compile_decompose o
     SIMP_RULE bool_ss [gas_shadow_expr_def]) >>
  rename1 `compile_get_target_ptr _ cenv bt sa = (rb,sm)` >>
  rename1 `compile_get_target_ptr _ _ (gas_shadow_target bt) shadow_sa = (rb',shadow_sm)` >>
  `rb' = rb /\ gas_shadow_state sm shadow_sm` by
    (irule gas_shadow_step >> rpt (first_assum (irule_at Any)) >>
     simp[gas_shadow_stmt_get_target_ptr_env]) >>
  qpat_x_assum `rb' = rb` SUBST_ALL_TAC >>
  rename1 `lower_value _ cenv _ e sm = (ix,sn)` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) shadow_sm = (ix',shadow_sn)` >>
  `ix' = ix /\ gas_shadow_state sn shadow_sn` by
    (irule gas_shadow_step >> rpt (first_assum (irule_at Any)) >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  qpat_x_assum `ix' = ix` SUBST_ALL_TAC >>
  `ci_mono shadow_sa shadow_sm /\ ci_mono shadow_sm shadow_sn /\
   ci_mono shadow_sn shadow_sb` by
    (irule target_subscript_compile_intervals >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  qexistsl_tac [`rb`,`sm`,`ix`,`sn`,`shadow_sm`,`shadow_sn`] >>
  simp[] >> irule target_subscript_interval_code >> simp[]
QED
