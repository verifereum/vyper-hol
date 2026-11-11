(*
 * The pointer twin of bodySimMain's induction: the cases for return, raise and assert.
 * Each is the pointer twin of the S1 case of the same name (bodySim*Cases),
 * over bodyPtrPreds's predicates; bodySimPtrMain's body_sim_ptr_mutual
 * uses them.
 *
 * TOP-LEVEL:
 *   body_return_none_case_ptr
 *   body_return_case_ptr
 *   body_raise_bare_case_ptr
 *   body_raise_unreachable_case_ptr
 *   body_raise_reason_case_ptr
 *   body_assert_case_ptr
 *   body_assert_unreachable_case_ptr
 *   body_assert_reason_case_ptr
 *)
Theory bodyPtrExitCases
Ancestors
  allocLimits allocLimitsProps
  bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST vyperInterpreter
  vyperState vyperContext vyperTypeCallGraph list
  bodySimStmtCases bodyExprPreFacts supportedStmts supportedExprs
  supportedStmtTraverse supportedExprTraverse vyperTypeSystem
  stmtSimDefs stmtSimProps stmtLowering compileEnv emitHelper emitHelperProps
  stmtAbortPtr stmtAssertPtr exprLoweringProps gasContext

val _ = Parse.hide "body";

(* ===== Cases ===== *)

(* The frame's RetQ (frame_ret_ok_ptr). *)
Theorem body_return_none_case_ptr:
  !cx. body_stmt_ptr_ok cx (Return NONE)
Proof
  rw[body_stmt_ptr_ok_def, frame_ret_ok_ptr_def] >>
  first_x_assum irule >> simp[same_frame_refl] >>
  qexists_tac `env` >> simp[]
QED

Theorem body_return_case_ptr:
  !cx e. body_expr_ptr_ok cx e ==> body_stmt_ptr_ok cx (Return (SOME e))
Proof
  rw[body_stmt_ptr_ok_def, frame_ret_ok_ptr_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  qpat_assum `body_stmt_safe _ _` (strip_assume_tac o
    SIMP_RULE std_ss [body_stmt_safe_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, supported_iterator_exists_def,
      supported_assert_exists_def, supported_raise_exists_def,
      supported_expr_exists_def, int_calls_stmt_def, int_calls_atarget_def,
      int_calls_iterator_def, int_calls_assert_reason_def, int_calls_raise_reason_def,
      listTheory.EVERY_APPEND, listTheory.EVERY_CONJ,
      DE_MORGAN_THM, GSYM expr_has_evm_run_def]) >>
  qpat_assum `stmt_exprs_ok _ _` (strip_assume_tac o
    SIMP_RULE std_ss [stmt_exprs_ok_def, alloc_limits_stmt_def,
      alloc_limits_iterator_def, alloc_limits_assert_def, alloc_limits_raise_def,
      alloc_limits_expr_def]) >>
  imp_res_tac alloc_limits_expr_not_extcode >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def,
         body_inv_def] >>
     qexists_tac `[]` >> simp[]) >>
  first_x_assum irule >> fs[body_expr_ptr_ok_def] >>
  conj_tac >- metis_tac[] >> qexists_tac `env` >> simp[]
QED

Theorem body_raise_bare_case_ptr:
  !cx. body_stmt_ptr_ok cx (Raise RaiseBare)
Proof
  rw[body_stmt_ptr_ok_def] >> irule compile_raise_frag_ptr >> simp[]
QED

Theorem body_raise_unreachable_case_ptr:
  !cx. body_stmt_ptr_ok cx (Raise RaiseUnreachable)
Proof
  rw[body_stmt_ptr_ok_def] >> irule compile_raise_frag_ptr >> simp[]
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_raise_reason_case_ptr:
  !cx e. body_expr_ptr_ok cx e ==> body_stmt_ptr_ok cx (Raise (RaiseReason e))
Proof
  cheat
QED

Theorem body_assert_case_ptr:
  !cx e. body_expr_ptr_ok cx e ==> body_stmt_ptr_ok cx (Assert e AssertBare)
Proof
  rw[body_stmt_ptr_ok_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def, supportedExprsTheory.supported_expr_def] >>
  qpat_assum `body_stmt_safe _ _` (strip_assume_tac o
    SIMP_RULE std_ss [body_stmt_safe_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, supported_iterator_exists_def,
      supported_assert_exists_def, supported_raise_exists_def,
      supported_expr_exists_def, int_calls_stmt_def, int_calls_atarget_def,
      int_calls_iterator_def, int_calls_assert_reason_def, int_calls_raise_reason_def,
      listTheory.EVERY_APPEND, listTheory.EVERY_CONJ,
      DE_MORGAN_THM, GSYM expr_has_evm_run_def]) >>
  qpat_assum `stmt_exprs_ok _ _` (strip_assume_tac o
    SIMP_RULE std_ss [stmt_exprs_ok_def, alloc_limits_stmt_def,
      alloc_limits_iterator_def, alloc_limits_assert_def, alloc_limits_raise_def,
      alloc_limits_expr_def]) >>
  imp_res_tac alloc_limits_expr_not_extcode >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_assert_exists_def, int_calls_stmt_def,
         int_calls_assert_reason_def, body_inv_def] >>
     qexists_tac `[]` >> simp[]) >>
  irule compile_assert_frag_ptr >> gvs[type_stmt_def] >>
  fs[body_expr_ptr_ok_def] >> metis_tac[compile_expr_grows]
QED

Theorem body_assert_unreachable_case_ptr:
  !cx e.
    body_expr_ptr_ok cx e ==> body_stmt_ptr_ok cx (Assert e AssertUnreachable)
Proof
  rw[body_stmt_ptr_ok_def] >>
  `supported_expr tops e` by gvs[supported_stmt_def, supportedExprsTheory.supported_expr_def] >>
  qpat_assum `body_stmt_safe _ _` (strip_assume_tac o
    SIMP_RULE std_ss [body_stmt_safe_def, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, supported_iterator_exists_def,
      supported_assert_exists_def, supported_raise_exists_def,
      supported_expr_exists_def, int_calls_stmt_def, int_calls_atarget_def,
      int_calls_iterator_def, int_calls_assert_reason_def, int_calls_raise_reason_def,
      listTheory.EVERY_APPEND, listTheory.EVERY_CONJ,
      DE_MORGAN_THM, GSYM expr_has_evm_run_def]) >>
  qpat_assum `stmt_exprs_ok _ _` (strip_assume_tac o
    SIMP_RULE std_ss [stmt_exprs_ok_def, alloc_limits_stmt_def,
      alloc_limits_iterator_def, alloc_limits_assert_def, alloc_limits_raise_def,
      alloc_limits_expr_def]) >>
  imp_res_tac alloc_limits_expr_not_extcode >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_assert_exists_def, int_calls_stmt_def,
         int_calls_assert_reason_def, body_inv_def] >>
     qexists_tac `[]` >> simp[]) >>
  irule compile_assert_frag_ptr >> gvs[type_stmt_def] >>
  fs[body_expr_ptr_ok_def] >> metis_tac[compile_expr_grows]
QED

(* ADMITTED: a piece of the body induction. *)
Theorem body_assert_reason_case_ptr:
  !cx e se.
    (!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> body_expr_ptr_ok cx se) /\
    body_expr_ptr_ok cx e ==>
    body_stmt_ptr_ok cx (Assert e (AssertReason se))
Proof
  cheat
QED
