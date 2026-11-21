(* Task-private syntax boundary for supported nonmutating internal callees. *)
Theory targetPureWalkCallees
Ancestors
  bodyIntCallSource bodyExprPreFacts supportedNames compileVyper loweringShapeProps
  vyperReadOnlySyntax vyperTypeCallGraph supportedStmtTraverse supportedExprTraverse
  supportedProgram supportedExprs exprLowering compileEnv vyperTypeContract list
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

Theorem target_walk_callee_syntax:
  cenv.ce_func_mutability = build_func_mutability (cx_tops cx) /\
  (!vis mut nr rr fn args dflts ret body.
     MEM (FunctionDecl vis mut nr rr fn args dflts ret body) (cx_tops cx) ==>
     function_mutability_ok [(NONE,cx_tops cx)] vis mut nr dflts body) /\
  supported_program (cx_tops cx) /\
  IS_SOME (supported_function_decl (cx_tops cx) (NONE,name) Internal) /\
  ~call_can_mutate cenv (IntCall (NONE,name)) /\
  lookup_callable_function cx.in_deploy name (cx_tops cx) =
    SOME (mut,nr,args,dflts,ret,body) /\
  int_calls_exprs dflts = [] /\ int_calls_stmts body = [] ==>
  EVERY (expr_mutability_ok [(NONE,cx_tops cx)] View) dflts /\
  int_calls_exprs dflts = [] /\ (mut = View \/ mut = Pure) /\
  stmts_mutability_ok [(NONE,cx_tops cx)] View body /\
  int_calls_stmts body = []
Proof
  strip_tac >> drule_all supported_internal_callable >> strip_tac >>
  `ALL_DISTINCT (supported_function_names (cx_tops cx))` by
    metis_tac[supported_program_def, supported_declaration_names_unique] >>
  drule_all target_walk_mutability_lookup >> strip_tac >>
  `mut = View \/ mut = Pure` by
    (Cases_on `mut` >> gvs[call_can_mutate_def, nsid_to_string_def]) >>
  `function_mutability_ok [(NONE,cx_tops cx)] Internal mut nr dflts body` by
    metis_tac[] >>
  gvs[function_mutability_ok_def, EVERY_MEM] >>
  metis_tac[expr_target_mutability_view, stmt_mutability_view]
QED
