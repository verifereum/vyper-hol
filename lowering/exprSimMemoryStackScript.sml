(* Stack adaptation retains counted memory execution and complete posts. *)
Theory exprSimMemoryStack
Ancestors
  exprSimMemDefs exprSimDefs exprSimStack loweringPosts gasOutcome gasSummary
  gasSummaryCompose gasContext gasExemptCert exprLowering emitHelper compileEnv
  vyperInterpreter vyperState fragExecMem

Theorem body_expr_vv_sim_mem_stack:
  expr_sim_mem ctx func cenv cx ty e es /\
  (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op,sb)) /\
  (!s tv es'. eval_expr cx e s = (INL tv,es') ==> ?v. tv = Value v) ==>
  expr_vv_sim_mem ctx func cenv cx ty e es
Proof
  strip_tac >> rw[expr_vv_sim_mem_def] >>
  qpat_x_assum `!sa. ?t op sb. _` (qspec_then `sa` strip_assume_tac) >> gvs[] >>
  `lower_value compile_expr cenv ty e sa = (op,sb)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  Cases_on `res`
  >- (rename1 `eval_expr cx e es = (INL raw,es')` >>
      `?v. raw = Value v` by metis_tac[] >> gvs[] >>
      qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
      disch_then (qspecl_then [`sa`, `sb`, `op`, `INL v`, `es'`, `s0`] mp_tac) >>
      simp[vyperStateTheory.bind_def, read_result_def,
           vyperStateTheory.return_def, expr_res_ok_def] >>
      strip_tac >> irule frag_exec_mem_conseq >> first_x_assum (irule_at Any) >>
      rpt strip_tac >>
      gvs[expr_post_def, vv_post_def, vv_holds_def, vv_at_def,
          read_result_def, vyperStateTheory.return_def] >>
      first_assum ACCEPT_TAC) >>
  rename1 `eval_expr cx e es = (INR exc,es')` >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sb`, `op`, `INR exc`, `es'`, `s0`] mp_tac) >>
  (impl_tac >- gvs[vyperStateTheory.bind_def, expr_res_ok_def, expr_vv_res_ok_def]) >>
  strip_tac >> irule frag_exec_mem_conseq >> first_x_assum (irule_at Any) >>
  simp[] >> rpt gen_tac >>
  Cases_on `exc` >> Cases_on `r` >> simp[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
QED
