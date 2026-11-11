(* Source and typing boundaries for the memory-counted tuple-local case. *)
Theory bodyMemAssignTupleLocalsPrep
Ancestors
  bodyMemAssignTupleLocalsFacts bodyMemoryPreds bodySim bodyExprPreFacts
  bodyRhsRoomMemory exprSimAggregateLayout vyperTypeArgFits
  supportedStmtTraverse supportedStmts supportedExprs vyperTypeSystem
  vyperTypeEnv exprSimHyps exprSimHypsDefs exprSimDefs gasContext
  vyperTypeCallGraph vyperTypeInvariants gasOutcome exprSimMemDefs
  stmtSimProps valueEncoding localPtrsProps exprLoweringProps loweringPosts
  venomState venomExecSemantics compileEnv finite_map list vyperLookup
  loweringSlice bodyMemoryDefs stmtSimAssignStore allocLimits
  valueTypingMemoryProps stmtSimDefs vyperState stmtLowering
  exprOperandVar freshWrites exprSimSource gasOracleReplay
  vyperTypeCallStackSoundness memoryLocalRhsProps stmtSimAugAssign stmtSimDeclStore
Libs
  monadsyntax

(* Restatement of S1 bodySimStmtCases.body_assign_tuple_rhs_pre [local]. *)
Theorem body_assign_tuple_rhs_pre:
  body_inv tops ctx cenv cx /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (TupleTarget gs) e) ==>
     occurs_abi_decode_target target tops) /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) ==>
  expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  `supported_expr tops e` by
    gvs[supported_stmt_def, supported_assignment_def] >>
  `well_typed_expr env e` by gvs[type_stmt_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
      is_dynamic (vyper_to_abi_type (type_env tops) target)` by
    gvs[body_inv_def] >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def, int_calls_stmt_def] >>
  qexists_tac `[]` >> simp[] >>
  metis_tac[call_evaluation_safe_append_right]
QED

(* The type/arity information used by the lowering code decomposition. *)
Theorem tuple_locals_source_types:
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty
    (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) = SOME env' ==>
  ?tys. expr_type e = TupleT tys /\ well_typed_expr env e /\
    assignable_type (get_tenv cx) (TupleT tys) /\
    LENGTH tys = LENGTH ids /\
    !i. i < LENGTH ids ==> FLOOKUP env.var_types (EL i ids) = SOME (EL i tys)
Proof
  strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  gvs[type_stmt_def, atarget_accepts_def, well_typed_atarget_def,
      LIST_REL_EL_EQN, EL_MAP, well_typed_target_def,
      well_typed_expr_def, AllCaseEqs()]
QED

