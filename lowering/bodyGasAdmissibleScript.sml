(* A checked function body's entry is admissible for every gas oracle. *)
Theory bodyGasAdmissible
Ancestors
  exprSimHypsDefs
  stmtSimDefs
  gasContext vyperState vyperTypeExprSoundness
  vyperTypeStmtSoundness vyperTypeEvalSoundness

Theorem body_stmts_gas_admissible:
  expr_sim_inv cenv cx env es /\
  type_stmts env ret_ty fbody = SOME env' /\
  call_evaluation_safe cx (int_calls_stmts fbody) /\
  stmts_no_control_escape fbody ==>
  gas_admissible (eval_stmts cx fbody) (stmt_res_ok NoLoop) es
Proof
  strip_tac >> rw[gas_admissible_def] >>
  `expr_sim_inv cenv cx env (es with gas_obs := gs)` by simp[] >>
  qpat_x_assum `expr_sim_inv _ _ _ (_ with gas_obs := _)`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def]) >>
  drule_all function_body_type_sound >>
  gvs[no_type_error_eval_def] >> strip_tac >>
  Cases_on `res`
  >- (rename1 `INL u` >> Cases_on `u` >> simp[stmt_res_ok_def]) >>
  rename1 `INR exc` >>
  `exc <> BreakException /\ exc <> ContinueException` by
    (drule_all stmts_no_control_escape_eval_stmts_no_loop_control >> simp[]) >>
  Cases_on `exc` >> gvs[stmt_res_ok_def, no_type_error_result_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[]
QED

