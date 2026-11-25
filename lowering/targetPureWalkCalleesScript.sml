(* Syntax and lookup facts for supported nonmutating internal callees. *)
Theory targetPureWalkCallees
Ancestors
  bodyIntCallSource bodyExprPreFacts supportedNames compileVyper loweringShapeProps
  vyperReadOnlySyntax vyperTypeCallGraph supportedStmtTraverse supportedExprTraverse
  supportedProgram supportedExprs exprLowering compileEnv vyperTypeContract list
  exprOracleStorageInterfaces bodyStorageCases vyperInterpreter

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

Theorem target_walk_callee_mutability:
  cenv.ce_func_mutability = build_func_mutability (cx_tops cx) /\
  supported_program (cx_tops cx) /\
  IS_SOME (supported_function_decl (cx_tops cx) (NONE,name) Internal) /\
  ~call_can_mutate cenv (IntCall (NONE,name)) /\
  lookup_callable_function cx.in_deploy name (cx_tops cx) =
    SOME (mut,nr,args,dflts,ret,body) ==>
  mut = View \/ mut = Pure
Proof
  strip_tac >> drule_all supported_internal_callable >> strip_tac >>
  `ALL_DISTINCT (supported_function_names (cx_tops cx))` by
    metis_tac[supported_program_def, supported_declaration_names_unique] >>
  drule_all target_walk_mutability_lookup >> strip_tac >>
  Cases_on `mut` >> gvs[call_can_mutate_def, nsid_to_string_def]
QED

Theorem target_walk_read_only_syntax:
  (!vis mut nr rr fn args dflts ret body.
     MEM (FunctionDecl vis mut nr rr fn args dflts ret body) tops ==>
     function_mutability_ok [(NONE,tops)] vis mut nr dflts body) /\
  supported_program tops /\
  IS_SOME (supported_function_decl tops (NONE,name) Internal) /\
  lookup_callable_function in_deploy name tops =
    SOME (mut,nr,args,dflts,ret,body) /\
  (mut = View \/ mut = Pure) ==>
  EVERY (expr_mutability_ok [(NONE,tops)] View) dflts /\
  stmts_mutability_ok [(NONE,tops)] View body /\
  EVERY (\c. FST c = NONE ==>
             IS_SOME (supported_function_decl tops c Internal)) (int_calls_exprs dflts) /\
  EVERY (\c. FST c = NONE ==>
             IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmts body)
Proof
  strip_tac >> drule_all supported_internal_callable >> strip_tac >>
  `function_mutability_ok [(NONE,tops)] Internal mut nr dflts body` by
    metis_tac[] >>
  (conj_tac
  >- (gvs[function_mutability_ok_def, EVERY_MEM] >>
      metis_tac[expr_target_mutability_view]) >>
  conj_tac
  >- (gvs[function_mutability_ok_def] >> metis_tac[stmt_mutability_view]) >>
  conj_tac >- metis_tac[supported_pure_main_calls |> cj 2] >>
  gvs[supported_function_body_def, body_stmts_safe_iff])
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
  strip_tac >> drule_all target_walk_callee_mutability >> disch_then assume_tac >>
  drule_all target_walk_read_only_syntax >> simp[]
QED

Theorem target_walk_supported_call_context:
  (!vis mut nr rr fn args dflts ret body.
     MEM (FunctionDecl vis mut nr rr fn args dflts ret body) tops ==>
     function_mutability_ok [(NONE,tops)] vis mut nr dflts body) /\
  supported_program tops /\ module_code NONE = SOME tops /\
  (!src. module_code (SOME src) = NONE) ==>
  !src fn ts. (src = NONE ==>
     IS_SOME (supported_function_decl tops (src,fn) Internal)) /\
     module_code src = SOME ts ==>
    ALOOKUP [(NONE,tops)] src = SOME ts /\
    lookup_callable_function in_deploy fn ts = lookup_callable_function F fn ts /\
    (!mut nr args dflts ret body.
       lookup_callable_function in_deploy fn ts = SOME (mut,nr,args,dflts,ret,body) /\
       (mut = View \/ mut = Pure) ==>
       EVERY (expr_mutability_ok [(NONE,tops)] View) dflts /\
       stmts_mutability_ok [(NONE,tops)] View body /\
       EVERY (\c. FST c = NONE ==>
                  IS_SOME (supported_function_decl tops c Internal)) (int_calls_exprs dflts) /\
       EVERY (\c. FST c = NONE ==>
                  IS_SOME (supported_function_decl tops c Internal)) (int_calls_stmts body))
Proof
  strip_tac >> rpt gen_tac >> Cases_on `src` >> simp[] >> strip_tac >> gvs[] >>
  conj_tac
  >- (Cases_on `supported_function_decl tops (NONE,fn) Internal` >>
      gvs[] >> PairCases_on `x` >>
      imp_res_tac supported_internal_lookup >> simp[lookup_callable_function_def]) >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN assume_tac) >>
  drule_all target_walk_read_only_syntax >> simp[]
QED
