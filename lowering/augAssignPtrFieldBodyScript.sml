(* Body-level local struct-field augmented assignment. *)
Theory augAssignPtrFieldBody
Ancestors
  augAssignPtrFieldCase exprSimProps stmtSimAugAssignAttr stmtSimAssignAttr bodyExprPreFacts
  bodyPtrPreds bodyPtrDefs bodySim exprSimAttributeFields exprSimFieldLayout
  supportedStmts exprSimHypsDefs vyperTypeEnv vyperTypeInvariants
  vyperTypeSystem vyperTyping vyperState vyperInterpreter vyperTypeCallGraph
  supportedStmtTraverse supportedExprTraverse gasContext compileEnv list finite_map

Theorem body_augassign_attr_local_ptr:
  !cx ty id fld bop e tops ctx PG func cenv env env' ret_ty lctx RetQ es.
    (!s0 p s1 s2 cur s3 s4 ptv s5.
       eval_target_place cx (AttributeTarget (NameTarget id) fld) s0 = (INL p,s1) /\
       read_place cx p s2 = (INL cur,s3) /\
       place_type_value cx p s4 = (INL ptv,s5) ==> body_expr_ptr_ok cx e) /\
    body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) ==>
       occurs_abi_decode_target target tops) /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
      (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)) es
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
         supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def, optionTheory.IS_SOME_EXISTS] >>
     qexists_tac `[]` >> simp[]) >>
  `?sid. FLOOKUP env.var_types id = SOME (StructT sid) /\
         attribute_type env.type_defs (StructT sid) fld = SOME ty /\
         well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn` by
    (gvs[type_stmt_def, well_typed_target_def,
         vyperTypeEnvTheory.type_place_target_AttributeTarget,
         vyperTypeEnvTheory.type_place_target_NameTarget] >>
     rename1 `attribute_type _ tgt_ty fld = SOME _` >>
     Cases_on `tgt_ty` >> gvs[attribute_type_def]) >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields
                    (nsid_to_string sid)) fld = SOME (ty,fsz)` by
    metis_tac[attribute_type_struct_field] >>
  `body_expr_ptr_ok cx e` by
    (drule_all augassign_attr_local_place >> strip_tac >>
     first_x_assum irule >> metis_tac[]) >>
  `(bop = Exp ==> nonneg_int_literal e) /\
   (bop = ShL \/ bop = ShR ==> shift_amount_ok e)` by
    gvs[type_stmt_def, well_typed_expr_def, DISJ_IMP_THM, AllCaseEqs()] >>
  irule compile_augassign_attr_local_case_ptr >> simp[] >> metis_tac[]
QED
