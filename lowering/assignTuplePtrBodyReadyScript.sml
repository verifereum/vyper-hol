(* Body-level readiness facts, shared by the tuple branch adapters. *)
Theory assignTuplePtrBodyReady
Ancestors
  bodySimStmtCases bodyPtrPreds bodySim exprSimHyps exprSimHypsDefs
  compileVyper vyperCompiler exprSimSource vyperTypeExprResult
  vyperTypeExprSoundness vyperTypeInvariants vyperTyping
  stmtSimAugAssign memoryLocalRhsProps exprSimAggregateLayout allocLimits allocLimitsProps tupleStageProps stmtSimReturn
  stmtSimDeclStore tupleTargetStoreProps valueCopyBytes vyperTypeSystem vyperTypeEnv
  vyperInterpreter vyperState vyperValue compileEnv exprLoweringProps
  stmtLowering loweringPosts list finite_map words arithmetic
Libs
  monadsyntax

Theorem tuple_target_local_ready_ptr:
  expr_sim_inv cenv cx env es /\ locals_alloc_ok cenv env /\
  FLOOKUP env.var_types id = SOME ty /\ 0 < type_memory_bytes cenv ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  ?p sz vt. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME vt /\
    if is_word_type ty then is_word_type vt else
      (vt = ty \/ is_bytestring_type vt /\ is_bytestring_type ty) /\
      type_memory_bytes cenv ty = type_memory_size tv /\
      ?vtv. evaluate_type (get_tenv cx) vt = SOME vtv /\
        type_memory_bytes cenv vt = type_memory_size vtv /\
        0 < type_memory_size vtv /\ type_memory_size vtv + 64 < dimword (:256)
Proof
  rpt strip_tac >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    metis_tac[expr_sim_inv_local] >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  qexistsl_tac [`p`, `sz`, `ty`] >> simp[] >>
  Cases_on `is_word_type ty` >> simp[] >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `type_memory_bytes cenv ty < 2 ** 64` by metis_tac[locals_alloc_ok_def] >>
  metis_tac[allocation_limit_word_room]
QED

Theorem tuple_target_local_value_layout_ptr:
  expr_sim_inv cenv cx env es1 /\ FLOOKUP env.var_types id = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  lookup_scopes id es1.scopes = SOME entry ==>
  if is_word_type ty then store_lays_out tv entry.type v else
    ?vt. cenv.ce_var_type id = SOME vt /\
      evaluate_type (get_tenv cx) vt = SOME entry.type /\ value_has_type entry.type v
Proof
  rpt strip_tac >>
  `evaluate_type (get_tenv cx) ty = SOME entry.type` by metis_tac[expr_sim_inv_local] >>
  `entry.type = tv` by metis_tac[optionTheory.SOME_11] >>
  `cenv.ce_var_type id = SOME ty` by fs[expr_sim_inv_def] >>
  IF_CASES_TAC >> simp[] >> metis_tac[store_lays_out_typed]
QED

Theorem tuple_staging_bound_ptr:
  expr_sim_inv cenv cx env es /\ stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  expr_type e = TupleT tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\ is_memory_view e ==>
  type_memory_size (TupleTV tvs) < dimword (:256)
Proof
  rpt strip_tac >>
  `type_memory_bytes cenv (TupleT tys) < 2 ** 64` by
    gvs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
  `type_memory_bytes cenv (TupleT tys) = type_memory_size (TupleTV tvs)` by
    metis_tac[expr_sim_inv_memory_size] >>
  `type_memory_size (TupleTV tvs) + 64 < dimword (:256)` by
    metis_tac[allocation_limit_word_room] >> decide_tac
QED

Theorem body_inv_mcopy_ptr:
  body_inv tops ctx cenv cx ==> cenv.ce_target CapMcopy
Proof
  rw[body_inv_def] >> Cases_on `cx.in_deploy` >> gvs[]
  >- (gvs[lower_vyper_deploy_unit_def, AllCaseEqs()] >>
      rpt (pairarg_tac >> gvs[]) >>
      gvs[run_deploy_lowering_def, AllCaseEqs(), lowering_policy_ok_def]) >>
  gvs[lower_vyper_runtime_unit_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[run_lowering_def, AllCaseEqs(), lowering_policy_ok_def]
QED

Theorem tuple_eval_bind_notation_ptr:
  vyperState$bind (eval_expr cx e) (read_result cx) =
  (do result <- eval_expr cx e; read_result cx result od)
Proof
  simp[vyperStateTheory.bind_def, FUN_EQ_THM]
QED

Theorem expr_body_pre_eval_gas_ptr:
  expr_body_pre cenv cx env e es /\
  vyperState$bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := obs) = (INL v, es') ==>
  expr_sim_inv cenv cx env es' /\ value_runtime_typed env (expr_type e) v
Proof
  rewrite_tac[tuple_eval_bind_notation_ptr] >> rpt strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := obs)` by simp[] >>
  drule_all (SRULE [ETA_THM] exprSimSourceTheory.expr_body_pre_eval) >>
  simp[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def,
       value_runtime_typed_def]
QED
