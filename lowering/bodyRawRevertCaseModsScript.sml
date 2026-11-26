(* The linked RawRevert case reuses the forced run for its stack judgment. *)
Theory bodyRawRevertCaseMods
Ancestors
  bodyFullPredsMods bodyRawRevertSourceCutMods bodyRawRevertValueRunMods
  bodyActionStackVVMods exprLowering compileEnv vyperAST vyperState vyperValue
Libs pairLib

Theorem body_raw_revert_case_full_mods:
  !mods exps cx ann args dflt.
    body_exprs_full_ok_mods mods exps cx args ==>
    body_expr_full_ok_mods mods exps cx (Call ann RawRevert args dflt)
Proof
  rpt gen_tac >> disch_tac >> simp[Once body_expr_full_ok_mods_def] >>
  rpt gen_tac >> strip_tac >> drule_then strip_assume_tac raw_revert_source_cut_mods >>
  gvs[body_exprs_full_ok_mods_def] >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ e`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  qpat_assum `!DF lo d PG src tops ctx sh f sf ce env ty es.
                _ ==> expr_sim_full_mods _ _ _ _ e _ /\ _`
    (drule_all_then strip_assume_tac) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call NoneT RawRevert [e] NONE) es` by
    (irule raw_revert_value_run_mods >> conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexists `cap` >> simp[]) >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule action_stack_vv_full_mods >>
  qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ RawRevert _ _) _` (irule_at Any) >>
  simp[] >> conj_tac
  >- (gen_tac >>
      simp[Once compile_expr_def, compile_call_def, expr_type_def,
           comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> simp[])) >>
  simp[bind_def, lift_option_type_def, raise_def, return_def, AllCaseEqs()]
QED
