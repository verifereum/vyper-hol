(* Linked evaluator cases for branch and statement sequence. *)
Theory bodyBranchSeqCasesMods
Ancestors
  bodyFullPredsMods bodyIfBranchCaseMods bodyStmtSeqBindMods
  bodyNormalHeadTailMods bodyBranchCellFrameMods bodyFullIfExpReach
  bodySim supportedStmts supportedStmtTraverse vyperSubscriptOverlap
  vyperTypeSystem vyperTypeCallGraph vyperTypeCallStackSoundness exprSimHypsDefs list

Theorem if_stmt_full_ok_mods:
  !mods exps cx e yes no.
    (!ctx cenv src tops env es bindings s ret_ty env'.
       contract_inv mods exps ctx cenv cx /\
       module_body_inv mods src tops cenv cx /\
       expr_sim_inv_mods mods cenv cx env es /\
       body_const_cells_agree_mods mods cx env es /\
       supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' ==>
       EVERY (source_body_call_supported cx) (int_calls_stmt s)) ==>
    (!s tv t st x t'. eval_expr cx e s = (INL tv,t) /\ push_scope st = (INL x,t') ==>
       body_stmts_full_ok_mods mods exps cx yes) /\
    (!s tv t st x t'. eval_expr cx e s = (INL tv,t) /\ push_scope st = (INL x,t') ==>
       body_stmts_full_ok_mods mods exps cx no) /\
    body_expr_full_ok_mods mods exps cx e ==>
    body_stmt_full_ok_mods mods exps cx (If e yes no)
Proof
  ACCEPT_TAC bodyIfBranchCaseModsTheory.if_stmt_full_ok_mods
QED

Theorem source_inv_gas_obs[local]:
  expr_sim_inv_mods mods cenv cx env (es with gas_obs := gs) <=>
  expr_sim_inv_mods mods cenv cx env es
Proof
  simp[expr_sim_inv_mods_def]
QED

Theorem stmts_cons_full_ok_mods:
  !mods exps cx s ss.
    (!es x es1. eval_stmt cx s es = (INL x,es1) ==>
       body_stmts_full_ok_mods mods exps cx ss) /\
    body_stmt_full_ok_mods mods exps cx s ==>
    body_stmts_full_ok_mods mods exps cx (s::ss)
Proof
  rpt gen_tac >> strip_tac >> pure_rewrite_tac[body_stmts_full_ok_mods_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmts _ _ (s::ss) = _` mp_tac >>
  pure_once_rewrite_tac[type_stmt_def] >>
  Cases_on `type_stmt env ret_ty s` >- simp[] >> fs[] >> strip_tac >>
  rename1 `type_stmt env ret_ty s = SOME env1` >>
  `stmts_exprs_ok cenv (s::ss)` by simp[] >>
  irule (REWRITE_RULE [MAP] stmt_frag_cons_bind_mods) >>
  rpt conj_tac
  >~ [`ctx_has_dalloca`]
  >- (rpt strip_tac >> drule_all body_inv_no_phi_mods >> simp[])
  >~ [`stmt_frag_full_mods _ _ _ _ _ _ (stmt_env _ _ _ (gas_shadow_stmt _)) _ _`]
  >- (qpat_x_assum `body_stmt_full_ok_mods _ _ _ _`
        (irule o REWRITE_RULE [body_stmt_full_ok_mods_def]) >>
      fs[supported_stmt_def, supported_stmt_expr_exists_def,
         accesses_stmt_def, int_calls_stmt_def] >>
      conj_tac >- (drule call_evaluation_safe_append_left >> simp[]) >>
      conj_tac >- (qexistsl_tac [`env`, `env1`] >> simp[]) >>
      qexistsl_tac [`bindings`, `src`, `tops`] >> simp[]) >>
  rpt strip_tac >>
  `expr_sim_inv_mods mods cenv cx env (es with gas_obs := gs)` by
    simp[source_inv_gas_obs] >>
  `body_const_cells_agree_mods mods cx env (es with gas_obs := gs)` by simp[] >>
  drule_all_then strip_assume_tac normal_head_tail_inputs_mods >>
  qpat_x_assum `!st mid. eval_stmt _ _ st = (INL (),mid) ==> _`
    (drule_then (irule o REWRITE_RULE [body_stmts_full_ok_mods_def])) >>
  simp[] >>
  conj_tac >- (qexistsl_tac [`env1`, `env'`] >> simp[]) >>
  qexistsl_tac [`bindings`, `src`, `tops`] >> simp[]
QED
