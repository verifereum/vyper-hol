(* Return-value composition through the body expression precondition. *)
Theory bodyReturnMemory
Ancestors
  bodyMemoryPreds bodyMemoryDefs bodySim bodyExprPreFacts exprSimHypsDefs gasContext
  supportedExprTraverse supportedStmtTraverse supportedStmts
  vyperInterpreter vyperTypeSystem vyperState vyperAST vyperTypeCallGraph

Theorem return_expr_body_pre[local]:
  !tops bindings ctx cenv cx env ret_ty e env' es.
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Return (SOME e)) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
                (Return (SOME e)) ==> occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Return (SOME e)) = SOME env' /\
    stmt_exprs_ok cenv (Return (SOME e)) /\
    call_evaluation_safe cx (int_calls_stmt (Return (SOME e))) ==>
    expr_body_pre cenv cx env e es
Proof
  rpt gen_tac >> strip_tac >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  irule stmt_expr_body_pre >>
  gvs[type_stmt_def, stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
      supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def,
      body_inv_def] >>
  qexists_tac `[]` >> simp[]
QED

(* Previous successful proof (before counted ABI coverage propagation):
Theorem body_return_mem_ok:
  !cx e. body_expr_mem_ok cx e ==> body_stmt_mem_ok cx (Return (SOME e))
Proof
  rw[body_stmt_mem_ok_def, frame_ret_ok_mem_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  first_x_assum irule >> fs[body_expr_mem_ok_def] >>
  conj_tac >- metis_tac[] >> qexists_tac `env` >> simp[]
QED
*)

Theorem body_return_mem_ok:
  !cx e. body_expr_mem_ok cx e ==> body_stmt_mem_ok cx (Return (SOME e))
Proof
  rw[body_stmt_mem_ok_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule return_expr_body_pre >> metis_tac[]) >>
  gvs[frame_ret_ok_mem_def] >>
  first_x_assum irule >>
  simp[same_frame_refl] >>
  conj_tac >- metis_tac[body_expr_mem_ok_def] >>
  qexists_tac `env` >> simp[]
QED

