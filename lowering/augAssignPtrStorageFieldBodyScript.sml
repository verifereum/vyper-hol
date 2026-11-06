(* Body-level storage/transient struct-field augmented assignment. *)
Theory augAssignPtrStorageFieldBody
Ancestors
  augAssignPtrStorageFieldCase stmtSimAugAssignAttrStorage stmtSimAssignAttrStorage
  bodyExprPreFacts bodyPtrPreds bodyPtrDefs bodySim exprSimProps
  exprSimAttributeFields exprSimFieldLayout exprSimHypsDefs
  supportedStmts supportedStmtTraverse supportedExprTraverse
  vyperTypeEnv vyperTypeInvariants vyperTypeSystem vyperTyping
  vyperState vyperInterpreter vyperTypeCallGraph gasContext compileEnv
  augAssignPtrToplevelMetadata bodyStorageMetadata stmtSimAssignAttr
  supportedExprForms supportedDecls

Theorem augassign_supported_storage_field_write_decl:
  supported_storage_field_write tops (src,id) fld ==>
  src = NONE /\ find_var_decl_by_name id tops <> NONE /\
  ?mut sid slot. MEM (VariableDecl Private mut id (StructT sid) slot) tops
Proof
  simp[supported_storage_field_write_def, supported_storage_fields_def] >>
  Cases_on `supported_variable_decl tops (src,id)` >> simp[] >>
  rename1 `SOME x` >> PairCases_on `x` >>
  Cases_on `x0` >> Cases_on `x1` >> Cases_on `x2` >> Cases_on `x3` >>
  simp[] >> strip_tac >> drule supported_variable_decl_mem >> strip_tac >>
  simp[] >> metis_tac[augassign_find_var_decl_storage_some]
QED

Theorem body_augassign_attr_storage_ptr:
  !cx ty src id fld bop e tops ctx PG func cenv env env' ret_ty lctx RetQ es.
    (!s0 p s1 s2 cur s3 s4 ptv s5.
       eval_target_place cx (AttributeTarget (TopLevelNameTarget (src,id)) fld) s0 = (INL p,s1) /\
       read_place cx p s2 = (INL cur,s3) /\
       place_type_value cx p s4 = (INL ptv,s5) ==> body_expr_ptr_ok cx e) /\
    body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign ty (AttributeTarget (TopLevelNameTarget (src,id)) fld) bop e) ==>
       occurs_abi_decode_target target tops) /\ supported_expr tops e /\
    expr_sim_inv cenv cx env es /\ supported_storage_field_write tops (src,id) fld /\
    type_stmt env ret_ty (AugAssign ty (AttributeTarget (TopLevelNameTarget (src,id)) fld) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty (AttributeTarget (TopLevelNameTarget (src,id)) fld) bop e) /\
    call_evaluation_safe cx (int_calls_stmt
      (AugAssign ty (AttributeTarget (TopLevelNameTarget (src,id)) fld) bop e)) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty (AttributeTarget (TopLevelNameTarget (src,id)) fld) bop e))
      (eval_stmt cx (AugAssign ty (AttributeTarget (TopLevelNameTarget (src,id)) fld) bop e)) es
Proof
  rpt strip_tac >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  drule augassign_supported_storage_field_write_decl >> strip_tac >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops /\
   ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)` by fs[body_inv_def] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `env.type_defs = get_tenv cx` by gvs[env_consistent_def, env_context_consistent_def] >>
  `expr_body_pre cenv cx env e es` by
    (`cx_tops cx = tops` by metis_tac[cx_tops_module] >>
     `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
        is_dynamic (vyper_to_abi_type (type_env tops) target)` by fs[body_inv_def] >>
     irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def] >>
     qexists_tac `[]` >> simp[]) >>
  `?tgt_ty. type_place_target env (TopLevelNameTarget (NONE,id)) = SOME (Type tgt_ty) /\
     attribute_type env.type_defs tgt_ty fld = SOME ty /\
     well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn` by
    gvs[type_stmt_def, well_typed_target_def, type_place_target_AttributeTarget, AllCaseEqs()] >>
  gvs[type_place_target_TopLevelNameTarget]
  >- (drule_all augassign_env_assignable_find_none >> strip_tac >> gvs[]) >>
  drule_all env_consistent_toplevel_storage_static >> strip_tac >>
  drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  `tgt_ty = StructT sid` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >> drule_all build_maps_variable >> strip_tac >>
  `?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld = SOME (ty,fsz)` by
    metis_tac[attribute_type_struct_field] >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  `body_expr_ptr_ok cx e` by
    (drule_all augassign_attr_storage_place >> strip_tac >> first_x_assum irule >> metis_tac[]) >>
  `(bop = Exp ==> nonneg_int_literal e) /\ (bop = ShL \/ bop = ShR ==> shift_amount_ok e)` by
    gvs[type_stmt_def, well_typed_expr_def, DISJ_IMP_THM, AllCaseEqs()] >>
  irule compile_augassign_attr_storage_case_ptr >> simp[] >> metis_tac[]
QED
