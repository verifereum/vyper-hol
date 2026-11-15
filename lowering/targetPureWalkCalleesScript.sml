(* Task-private syntax boundary for supported nonmutating internal callees. *)
Theory targetPureWalkCallees
Ancestors
  bodyIntCallSource bodyExprPreFacts supportedNames compileVyper loweringShapeProps
  vyperReadOnlySyntax vyperTypeCallGraph supportedStmtTraverse supportedExprTraverse
  supportedProgram exprLowering compileEnv vyperTypeContract list
  exprOracleStorageInterfaces

val _ = Parse.hide "body";

Theorem target_walk_mutability_lookup[local]:
  !tops mut nr rr name args dflts ret body.
    ALL_DISTINCT (supported_function_names tops) /\
    MEM (FunctionDecl Internal mut nr rr name args dflts ret body) tops ==>
    build_func_mutability tops name = mut
Proof
  Induct_on `tops` >- simp[] >>
  Cases_on `h` >>
  simp[supported_function_names_def, build_func_mutability_def] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac (iffRL MEM_supported_function_names) >>
  rpt IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem target_walk_assignment_no_calls[local]:
  (!t. ~supported_assignment_exists expr_internal_call_root t ==>
       int_calls_atarget t = []) /\
  (!ts. ~supported_assignments_exists expr_internal_call_root ts ==>
        int_calls_atargets ts = [])
Proof
  ho_match_mp_tac int_calls_atarget_ind >>
  simp[int_calls_atarget_def, supported_assignment_exists_def,
       no_internal_call_int_calls]
QED

Theorem target_walk_iterator_no_calls[local]:
  !iter. ~supported_iterator_exists expr_internal_call_root iter ==>
         int_calls_iterator iter = []
Proof
  Cases >> simp[supported_iterator_exists_def, int_calls_iterator_def,
                no_internal_call_int_calls]
QED

Theorem target_walk_assert_no_calls[local]:
  !reason. ~supported_assert_exists expr_internal_call_root reason ==>
           int_calls_assert_reason reason = []
Proof
  Cases >> simp[supported_assert_exists_def, int_calls_assert_reason_def,
                no_internal_call_int_calls, int_calls_exprs_empty_every,
                EVERY_MEM, EXISTS_MEM] >> metis_tac[no_internal_call_int_calls]
QED

Theorem target_walk_raise_no_calls[local]:
  !reason. ~supported_raise_exists expr_internal_call_root reason ==>
           int_calls_raise_reason reason = []
Proof
  Cases >> simp[supported_raise_exists_def, int_calls_raise_reason_def,
                no_internal_call_int_calls, int_calls_exprs_empty_every,
                EVERY_MEM, EXISTS_MEM] >> metis_tac[no_internal_call_int_calls]
QED

Theorem target_walk_stmts_no_calls[local]:
  (!s. ~supported_stmt_expr_exists expr_internal_call_root s ==>
       int_calls_stmt s = []) /\
  (!ss. ~supported_stmts_expr_exists expr_internal_call_root ss ==>
        int_calls_stmts ss = [])
Proof
  ho_match_mp_tac int_calls_stmt_ind >>
  simp[int_calls_stmt_def, supported_stmt_expr_exists_def,
       no_internal_call_int_calls, target_walk_assignment_no_calls,
       target_walk_iterator_no_calls, target_walk_assert_no_calls,
       target_walk_raise_no_calls]
QED

Theorem target_walk_callee_syntax:
  cenv.ce_func_mutability = build_func_mutability (cx_tops cx) /\
  (!vis mut nr rr fn args dflts ret body.
     MEM (FunctionDecl vis mut nr rr fn args dflts ret body) (cx_tops cx) ==>
     function_mutability_ok [(NONE,cx_tops cx)] vis mut nr dflts body) /\
  supported_program (cx_tops cx) /\
  IS_SOME (supported_function_decl (cx_tops cx) (NONE,name) Internal) /\
  ~call_can_mutate cenv (IntCall (NONE,name)) /\
  lookup_callable_function cx.in_deploy name (cx_tops cx) =
    SOME (mut,nr,args,dflts,ret,body) ==>
  dflts = [] /\ (mut = View \/ mut = Pure) /\
  stmts_mutability_ok [(NONE,cx_tops cx)] View body /\
  int_calls_stmts body = []
Proof
  strip_tac >> drule_all supported_internal_callable >> strip_tac >>
  `ALL_DISTINCT (supported_function_names (cx_tops cx))` by
    metis_tac[supported_program_def, supported_declaration_names_unique] >>
  drule_all target_walk_mutability_lookup >> strip_tac >>
  `mut = View \/ mut = Pure` by
    (Cases_on `mut` >> gvs[call_can_mutate_def, nsid_to_string_def]) >>
  `function_mutability_ok [(NONE,cx_tops cx)] Internal mut nr [] body` by
    metis_tac[] >>
  gvs[function_mutability_ok_def] >>
  metis_tac[stmt_mutability_view, target_walk_stmts_no_calls,
            supported_internal_body_contract]
QED
