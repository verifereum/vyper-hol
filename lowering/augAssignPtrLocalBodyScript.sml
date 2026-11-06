(* Body-level live local augmented assignment. *)
Theory augAssignPtrLocalBody
Ancestors
  augAssignPtrLocalCase exprSimProps stmtSimAugAssign bodyExprPreFacts bodyPtrPreds bodyPtrDefs bodySim
  supportedStmts exprSimHypsDefs vyperTypeEnv vyperTypeInvariants
  vyperTypeSystem vyperTyping vyperState vyperInterpreter vyperTypeCallGraph
  supportedStmtTraverse supportedExprTraverse gasContext compileEnv list finite_map

Theorem body_augassign_local_ptr:
  !cx ty id bop e tops ctx PG func cenv env env' ret_ty lctx RetQ es.
    (!s0 p s1 s2 cur s3 s4 ptv s5.
       eval_target_place cx (NameTarget id) s0 = (INL p,s1) /\
       read_place cx p s2 = (INL cur,s3) /\
       place_type_value cx p s4 = (INL ptv,s5) ==> body_expr_ptr_ok cx e) /\
    body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign ty (NameTarget id) bop e) ==>
       occurs_abi_decode_target target tops) /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AugAssign ty (NameTarget id) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty (NameTarget id) bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty (NameTarget id) bop e)) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty (NameTarget id) bop e))
      (eval_stmt cx (AugAssign ty (NameTarget id) bop e)) es
Proof
  rpt strip_tac >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops` by fs[body_inv_def] >>
  `expr_body_pre cenv cx env e es` by
    (`cx_tops cx = tops` by metis_tac[cx_tops_module] >>
     `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
        is_dynamic (vyper_to_abi_type (type_env tops) target)` by fs[body_inv_def] >>
     irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  `FLOOKUP env.var_types id = SOME ty /\
   well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
   (bop = Exp ==> nonneg_int_literal e) /\
   (bop = ShL ==> shift_amount_ok e) /\ (bop = ShR ==> shift_amount_ok e)` by
    (gvs[type_stmt_def, well_typed_target_def, well_typed_expr_def,
         DISJ_IMP_THM, AllCaseEqs()] >>
     Cases_on `FLOOKUP env.var_types id` >>
     Cases_on `FLOOKUP env.var_assignable id` >> gvs[] >>
     rename1 `FLOOKUP env.var_assignable id = SOME asg` >>
     Cases_on `asg` >> gvs[]) >>
  drule_all expr_sim_inv_local >> strip_tac >>
  `body_expr_ptr_ok cx e` by
    (first_x_assum irule >> metis_tac[stmtSimAugAssignTheory.eval_target_place_local]) >>
  irule compile_augassign_local_case_ptr >> simp[DISJ_IMP_THM] >>
  conj_tac >- (qexists_tac `tops` >> simp[]) >>
  qexists_tac `env` >> simp[]
QED
