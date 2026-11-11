(* Memory-safe declaration of a widened aggregate internal-call result. *)
Theory bodyMemAnnAssignWidened
Ancestors
  widenedDeclarationIntegrationMem
  assignValueMemoryOpen exprOpenMain exprOpenTerminals
  bodyMemoryPreds widenedLocalContinuationMem widenedLocalOutcomeMem
  widenedAssignValueParts widenedLocalRuntimeMem widenedDeclareContinuationMem
  bodyExprPreFacts supportedStmtTraverse supportedStmts vyperTypeInvariants
  vyperTypeSystem vyperTypeExprResult vyperTyping bodySim exprSimHypsDefs
  gasContext supportedTypes vyperInterpreter vyperTypeCallGraph vyperState
  bodyDeclMemoryCounted bodyDeclCopyMemory stmtSimDeclCompose stmtSimDecl
  stmtSimDeclMem exprLoweringProps exprSimProps stmtSimProps stmtSimDefs
  bodySimDeclCases exprSimIfExpCompat exprSimSource compileEnv fragExec
  stmtSimDeclSource exprSimMemorySource exprSimMemDefs widenedValueReadOutcomeMem
Libs
  monadsyntax

Theorem body_annassign_widened_aggregate_call_mem:
  !d cx id typ e tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv,t) ==>
       body_expr_mem_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AnnAssign id typ e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    ~is_word_type typ /\ 0 < type_memory_bytes cenv typ /\
    ~(lowered_value_type cenv e = expr_type e \/
      is_bytestring_type (expr_type e) /\
      is_bytestring_type (lowered_value_type cenv e) /\
      arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
      (eval_stmt cx (AnnAssign id typ e)) es
Proof
  rpt gen_tac >> strip_tac >>
  `supported_expr tops e /\ supported_copy_types typ (expr_type e)` by
    gvs[supported_stmt_def] >>
  `well_typed_expr env e /\ assignable_type env.type_defs typ /\
   type_widens_to env.type_defs (expr_type e) typ /\
   id NOTIN FDOM env.var_types` by gvs[type_stmt_def, AllCaseEqs()] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    metis_tac[assignable_type_well_formed, well_formed_type_def,
              optionTheory.IS_SOME_EXISTS] >>
  `body_expr_mem_ok cx e` by
    (first_x_assum irule >> simp[lift_option_type_def, return_def]) >>
  `expr_body_pre cenv cx env e es` by
    (drule_then strip_assume_tac supported_expr_body_calls >>
     `cx_tops cx = tops` by (irule cx_tops_module >> fs[body_inv_def]) >>
     irule stmt_expr_body_pre >>
     gvs[body_inv_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         int_calls_stmt_def] >> qexists_tac `[]` >> simp[]) >>
  irule widened_declaration_integration_mem >> metis_tac[]
QED
