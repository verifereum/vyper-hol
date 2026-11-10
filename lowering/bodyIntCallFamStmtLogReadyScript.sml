(* Source readiness for the resource-carrying Log traversal. *)
Theory bodyIntCallFamStmtLogReady
Ancestors
  exprSimHypsDefs bodyExprPreFacts bodySim supportedExprTraverse
  supportedStmtTraverse supportedStmts vyperTypeSystem list

Theorem expr_body_pre_state_transport:
  expr_body_pre ce cx env e es /\ expr_sim_inv ce cx env ee ==>
  expr_body_pre ce cx env e ee
Proof
  simp[expr_body_pre_def]
QED

Theorem intcall_log_args_body_pre:
  body_inv tops ctx ce cx /\ supported_log tops id args /\
  type_stmt env ret_ty (Log id args) = SOME env' /\
  stmt_exprs_ok ce (Log id args) /\ expr_sim_inv ce cx env es /\
  call_evaluation_safe cx (int_calls_exprs args) /\ 
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Log id args) ==> occurs_abi_decode_target target tops) ==>
  EVERY (\e. expr_body_pre ce cx env e es) args
Proof
  strip_tac >>
  `get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  `cx_tops cx = tops` by metis_tac[gasContextTheory.cx_tops_module] >>
  `well_typed_exprs env args` by
    fs[type_stmt_def, AllCaseEqs()] >>
  fs[supported_log_def, supportedExprsTheory.supported_pure_exprs_every,
     stmt_exprs_ok_def,
     supported_stmt_expr_exists_def, supported_exprs_exists_every, EVERY_MEM] >>
  rpt strip_tac >>
  `supportedExprs$supported_expr tops e` by
    metis_tac[supportedExprsTheory.supported_expr_def] >>
  drule supported_expr_body_calls >> strip_tac >>
  `int_calls_expr e = []` by metis_tac[supported_pure_int_calls] >>
  irule stmt_expr_body_pre >>
  simp[] >> rpt conj_tac
  >- (fs[body_inv_def])
  >- (fs[EXISTS_MEM] >> metis_tac[])
  >- (qexists_tac `[]` >>
      irule vyperTypeCallStackSoundnessTheory.call_evaluation_safe_mono >>
      qexists_tac `int_calls_exprs args` >> simp[])
  >> metis_tac[exprSimSourceTheory.well_typed_exprs_member]
QED
