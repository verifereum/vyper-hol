(* Linked target compilation: the same base and key operands on both cuts. *)
Theory bodyWriteMapCompileCutsMods
Ancestors
  bodyWriteTargetStageMods targetSubscriptContinuation gasShadowCompileStmtHelpers
  bodyFullShared exprLoweringProps exprLowering gasShadow gasShadowState fragExec
  vyperAST compileEnv

Theorem shadow_cut_result[local]:
  gas_shadow_compiles f g ==>
  f s = (x,s') /\ gas_shadow_state s t ==>
  ?t'. g t = (x,t') /\ gas_shadow_state s' t'
Proof
  strip_tac >> strip_tac >> Cases_on `g t` >>
  drule_all gas_shadow_step >> simp[]
QED

Theorem subscript_known_intervals[local]:
  compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa = (r,sb) /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
  lower_value compile_expr cenv (expr_type e) e sm = (iop,sn) /\
  fn_has_code sa sb func ==>
  ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb /\
  fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func
Proof
  strip_tac >>
  qpat_assum `compile_get_target_ptr _ _ (SubscriptTarget _ _) _ = _`
    (mp_tac o MATCH_MP target_subscript_compile_decompose) >>
  simp[] >> strip_tac >>
  drule_all target_subscript_compile_intervals >> strip_tac >>
  drule_all target_subscript_interval_code >> simp[]
QED

Theorem write_map_compile_cuts_mods:
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (SubscriptTarget bt e) es st0 sa sb shadow_sa shadow_sb r s0 G0 tn0 ==>
  ?rb sm iop sn shadow_sm shadow_sn.
    write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx bt es st0 sa sm shadow_sa shadow_sm rb s0 G0 tn0 /\
    compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa = (r,sb) /\
    compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
    lower_value compile_expr cenv (expr_type e) e sm = (iop,sn) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) shadow_sm = (iop,shadow_sn) /\
    gas_shadow_state sm shadow_sm /\ gas_shadow_state sn shadow_sn /\
    fn_has_code sm sn func /\ fn_has_code shadow_sm shadow_sn shadow_func /\
    fn_has_code sn sb func /\
    ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb
Proof
  rewrite_tac[write_target_entry_mods_def] >> strip_tac >>
  qpat_assum `compile_get_target_ptr _ cenv (SubscriptTarget _ _) sa = _`
    (strip_assume_tac o MATCH_MP target_subscript_compile_decompose) >>
  rename1 `lower_value _ _ _ e sm = (iop,sn)` >>
  `?shadow_sm. compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
      (gas_shadow_target bt) shadow_sa = (rb,shadow_sm) /\
      gas_shadow_state sm shadow_sm` by
    (irule (MATCH_MP shadow_cut_result gas_shadow_stmt_get_target_ptr_env) >>
     qexists_tac `sa` >> simp[]) >>
  `?shadow_sn. lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) shadow_sm = (iop,shadow_sn) /\
      gas_shadow_state sn shadow_sn` by
    (irule (MATCH_MP shadow_cut_result gas_shadow_stmt_lower_value_env) >>
     qexists_tac `sm` >> simp[]) >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb /\
   fn_has_code sa sm func /\ fn_has_code sm sn func /\ fn_has_code sn sb func` by
    (drule_all target_subscript_compile_intervals >> strip_tac >>
     drule_all target_subscript_interval_code >> simp[]) >>
  `ci_mono shadow_sa shadow_sm /\ ci_mono shadow_sm shadow_sn /\
   ci_mono shadow_sn shadow_sb /\ fn_has_code shadow_sa shadow_sm shadow_func /\
   fn_has_code shadow_sm shadow_sn shadow_func /\
   fn_has_code shadow_sn shadow_sb shadow_func` by
    (irule subscript_known_intervals >> simp[] >>
     qexistsl_tac [`gas_shadow_target bt`,`gas_shadow_env T cenv`,
                   `gas_shadow_expr e`,`iop`,`r`,`rb`] >>
     fs[gas_shadow_expr_def,gas_shadow_expr_type]) >>
  qexistsl_tac [`rb`,`sm`,`iop`,`sn`,`shadow_sm`,`shadow_sn`] >>
  asm_rewrite_tac[] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED
