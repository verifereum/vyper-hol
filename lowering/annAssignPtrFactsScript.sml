(* Source and environment boundaries shared by pointer-safe declarations. *)
Theory annAssignPtrFacts
Ancestors
  supportedExprTraverse allocLimits allocLimitsProps
  bodyPtrPreds bodySimDeclCases bodyExprPreFacts exprSimSource
  exprSimHypsDefs bodySim stmtSimProps exprSimHyps exprLoweringProps
  vyperTyping vyperTypeCallGraph supportedStmts supportedStmtTraverse gasContext
  vyperInterpreter vyperState vyperAST list finite_map
  exprSimAggregateLayout vyperTypeSystem vyperTypeInvariants
  typedCopyMetadata supportedTypes context compileEnv

Theorem annassign_rhs_pre_ptr:
  !cenv cx env e es tops id typ ctx.
    body_stmt_safe tops (AnnAssign id typ e) /\
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) ==>
    expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
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
  `cx_tops cx = tops` by
    (irule cx_tops_module >> fs[body_inv_def]) >>
  irule stmt_expr_body_pre >>
  gvs[body_inv_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      int_calls_stmt_def] >>
  qexists_tac `[]` >> simp[]
QED

Theorem annassign_declared_rhs_pre_ptr:
  !cenv cx env e es tops id typ st c st1 ctx.
    body_stmt_safe tops (AnnAssign id typ e) /\
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    id NOTIN FDOM env.var_types /\ FLOOKUP cenv.ce_vars id = NONE /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    declare_local cenv id typ st = (c,st1) ==>
    body_inv tops ctx c cx /\ expr_body_pre c cx env e es
Proof
  rpt strip_tac >>
  `cenv.ce_alloca_locals` by fs[body_inv_def] >>
  `same_frame cenv c` by
    (drule_then irule declare_local_same_frame >> simp[]) >>
  `body_inv tops ctx c cx` by metis_tac[body_inv_same_frame] >>
  `stmt_exprs_ok c (AnnAssign id typ e)` by
    metis_tac[stmt_exprs_ok_same_frame] >>
  `expr_sim_inv c cx env es` by metis_tac[expr_sim_inv_declare_local] >>
  irule annassign_rhs_pre_ptr >> metis_tac[]
QED

Theorem annassign_declared_expr_sim_ptr:
  !cenv cx env e es tops id typ st c st1 ctx func d PG.
    body_stmt_safe tops (AnnAssign id typ e) /\
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    id NOTIN FDOM env.var_types /\ FLOOKUP cenv.ce_vars id = NONE /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    body_expr_ptr_ok cx e /\ declare_local cenv id typ st = (c,st1) ==>
    expr_sim_ptr d ctx PG func c cx (expr_type e) e es
Proof
  rpt strip_tac >>
  drule_all annassign_declared_rhs_pre_ptr >> strip_tac >>
  fs[body_expr_ptr_ok_def] >> metis_tac[]
QED

Theorem annassign_declared_expr_vv_sim_ptr:
  !cenv cx env e es tops id typ st c st1 ctx func d PG.
    body_stmt_safe tops (AnnAssign id typ e) /\
    body_inv tops ctx cenv cx /\ supported_expr tops e /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AnnAssign id typ e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
    id NOTIN FDOM env.var_types /\ FLOOKUP cenv.ce_vars id = NONE /\
    stmt_exprs_ok cenv (AnnAssign id typ e) /\
    call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e)) /\
    body_expr_ptr_ok cx e /\ declare_local cenv id typ st = (c,st1) ==>
    expr_vv_sim_ptr d ctx PG func c cx (expr_type e) e es
Proof
  rpt strip_tac >>
  drule_all annassign_declared_rhs_pre_ptr >> strip_tac >>
  fs[body_expr_ptr_ok_def] >> metis_tac[]
QED

Theorem annassign_memory_bytes_pos_ptr:
  !cenv cx env es ret_ty id typ e env'.
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' ==>
    0 < type_memory_bytes cenv typ
Proof
  rpt strip_tac >>
  `assignable_type env.type_defs typ` by gvs[type_stmt_def, AllCaseEqs()] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  irule exprSimAggregateLayoutTheory.expr_sim_inv_memory_bytes_pos >>
  metis_tac[]
QED

Theorem annassign_ih_ptr:
  !cx id typ e env ret_ty env' cenv es.
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
         (INL tyv,t) ==> body_expr_ptr_ok cx e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AnnAssign id typ e) = SOME env' ==>
    body_expr_ptr_ok cx e
Proof
  rpt strip_tac >>
  `assignable_type env.type_defs typ` by gvs[type_stmt_def, AllCaseEqs()] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type (get_tenv cx) typ = SOME tyv` by
    metis_tac[assignable_type_well_formed, well_formed_type_def,
              optionTheory.IS_SOME_EXISTS] >>
  first_x_assum irule >>
  qexistsl_tac [`es`, `es`, `get_tenv cx`, `tyv`] >>
  simp[lift_option_type_def, return_def]
QED

Theorem copy_types_not_word_bytestring_ptr:
  !dst src.
    supported_copy_types dst src /\ dst <> src /\ ~is_word_type dst ==>
    is_bytestring_type dst
Proof
  simp[supportedTypesTheory.supported_copy_types_def] >> rpt strip_tac
  >- metis_tac[typedCopyMetadataTheory.supported_word_type_is_word] >>
  Cases_on `dst` >> Cases_on `src` >> gvs[] >>
  rename1 `BaseT b` >> Cases_on `b` >>
  gvs[is_bytestring_type_def, is_word_type_def] >>
  Cases_on `b'` >> gvs[is_bytestring_type_def, AllCaseEqs()] >>
  Cases_on `b` >> gvs[] >> Cases_on `b''` >> gvs[is_bytestring_type_def]
QED
