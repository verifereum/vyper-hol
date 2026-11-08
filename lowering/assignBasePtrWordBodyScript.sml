(* Body-level word-local wrapper, with the source layout checked at the RHS endpoint. *)
Theory assignBasePtrWordBody
Ancestors assignBasePtrWordFragment assignTuplePtrBodyReady bodyPtrPreds bodyPtrDefs
  bodySim vyperTypeCallGraph exprSimSource bodyExprPreFacts
  stmtSimAssign stmtSimAssignStore stmtSimDeclStore exprSimHypsDefs
  exprSimHyps stmtSimProps stmtSimDefs exprSimDefs loweringPosts
  supportedStmtTraverse supportedStmts supportedExprs
  vyperTypeExprResult vyperTypeExprSoundness vyperTypeInvariants
  vyperTypeSystem vyperLookup vyperInterpreter vyperState
  compileEnv valueEncodingProps finite_map list gasContext
Libs monadsyntax

Theorem body_assign_local_word_ptr:
  !cx id e ty d ctx PG func tops bindings cenv env env' ret_ty lctx RetQ es.
    body_expr_ptr_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget (NameTarget id)) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    FLOOKUP env.var_types id = SOME ty /\ is_word_type ty ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt strip_tac >>
  `supported_expr tops e` by
    gvs[supported_stmt_def, supported_assignment_def] >>
  `well_typed_expr env e /\ expr_type e = ty` by
    (gvs[type_stmt_def, atarget_accepts_def, well_typed_expr_def, AllCaseEqs()] >>
     Cases_on `FLOOKUP env.var_assignable id` >> gvs[] >>
     rename1 `FLOOKUP env.var_assignable id = SOME asg` >>
     Cases_on `asg` >> gvs[] >> metis_tac[type_widens_to_word]) >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_assignment_exists_def, int_calls_stmt_def,
         int_calls_atarget_def, int_calls_expr_def, body_inv_def] >>
     qexists_tac `[]` >> simp[]) >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    metis_tac[expr_sim_inv_def] >>
  `cenv.ce_var_type id = SOME ty` by metis_tac[expr_sim_inv_def] >>
  `expr_sim_ptr d ctx PG func cenv cx ty e es` by metis_tac[body_expr_ptr_ok_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?etv. evaluate_type (get_tenv cx) ty = SOME etv` by
    (gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
     `IS_SOME (lookup_scopes id es.scopes)` by metis_tac[] >>
     gvs[optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
  irule compile_assign_local_stmt_frag_ptr >> simp[] >>
  suspend "layout"
QED

Resume body_assign_local_word_ptr[layout]:
  rpt strip_tac >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all expr_body_pre_eval_gas_ptr >> strip_tac >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def,
      value_runtime_typed_def] >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME entry.type` by
    (qpat_x_assum `expr_sim_inv _ _ _ es1`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_def,
          env_consistent_def, env_scopes_consistent_def]) >>
     qpat_x_assum `!id ty entry. _ /\ lookup_scopes _ es1.scopes = _ ==> _` irule >>
     qexists_tac `id` >> simp[]) >>
  gvs[] >> metis_tac[store_lays_out_typed]
QED
Finalise body_assign_local_word_ptr
