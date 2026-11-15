(* Augmented assignment to storage words of arbitrary supported width. *)
Theory bodyPtrAugAssignNarrow
Ancestors
  augAssignPtrToplevelCase augAssignPtrToplevelMetadata bodyAugAssignOther
  bodyStorageMetadata bodyExprPreFacts bodyPtrPreds bodyPtrDefs bodySim
  supportedStmts exprSimHypsDefs exprSimTopLevelProps stmtSimAugAssignStorage
  stmtSimAugAssign
  vyperTypeEnv vyperTypeInvariants vyperTypeSystem vyperTyping vyperState
  vyperInterpreter vyperTypeCallGraph supportedStmtTraverse supportedExprTraverse
  gasContext compileVyper compileEnv list finite_map

Theorem body_augassign_toplevel_aug_ptr:
  !cx ty src id bop e tops bindings ctx PG func cenv env env' ret_ty lctx RetQ es.
    (!s0 p s1 s2 cur s3 s4 ptv s5.
       eval_target_place cx (TopLevelNameTarget (src,id)) s0 = (INL p,s1) /\
       read_place cx p s2 = (INL cur,s3) /\
       place_type_value cx p s4 = (INL ptv,s5) ==> body_expr_ptr_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_aug_target tops bindings (TopLevelNameTarget (src,id)) /\
    supported_expr tops e /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign ty (TopLevelNameTarget (src,id)) bop e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget (src,id)) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty (TopLevelNameTarget (src,id)) bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty (TopLevelNameTarget (src,id)) bop e)) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty (TopLevelNameTarget (src,id)) bop e))
      (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e)) es
Proof
  rpt strip_tac >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  drule supported_aug_toplevel_decl >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `vis` (qx_choose_then `mut`
      (qx_choose_then `dty` (qx_choose_then `init` assume_tac))))) >>
  `find_var_decl_by_name id tops <> NONE` by
    metis_tac[augassign_find_var_decl_storage_some] >>
  gvs[] >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops /\
   ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)` by
    fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `type_place_target env (TopLevelNameTarget (NONE,id)) = SOME (Type ty) /\
   well_typed_expr env e /\ assignable_type env.type_defs ty /\
   well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
   (bop = Exp ==> nonneg_int_literal e) /\
   (bop = ShL ==> shift_amount_ok e) /\ (bop = ShR ==> shift_amount_ok e)` by
    (gvs[type_stmt_def, well_typed_target_def, DISJ_IMP_THM, AllCaseEqs()] >>
     drule stmtSimAugAssignTheory.augassign_operand_ok_operands >>
     simp[DISJ_IMP_THM]) >>
  `FLOOKUP env.bare_global_assignable (NONE,id) = NONE` by
    (Cases_on `FLOOKUP env.bare_global_assignable (NONE,id)` >> simp[] >>
     drule_all augassign_env_assignable_find_none >> strip_tac >> gvs[]) >>
  gvs[type_place_target_TopLevelNameTarget] >>
  drule_all env_consistent_toplevel_storage_static >> strip_tac >>
  drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  `dty = ty` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `lookup_var_slot_from_layout _ _ _ _ = SOME slot` >>
  rename1 `evaluate_type _ ty = SOME tvt` >>
  rename1 `find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,_)` >>
  `expr_body_pre cenv cx env e es` by
    (`cx_tops cx = tops` by metis_tac[cx_tops_module] >>
     `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
        is_dynamic (vyper_to_abi_type (type_env tops) target)` by fs[body_inv_def] >>
     irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def,
         optionTheory.IS_SOME_EXISTS] >>
     qexists_tac `[]` >> simp[]) >>
  `?v. read_storage_slot cx tr (n2w slot) tvt es = (INL v,es)` by
    (irule toplevel_storage_read_decodes >> fs[expr_body_pre_def, expr_sim_inv_def] >>
     metis_tac[]) >>
  `body_expr_ptr_ok cx e` by
    (drule_all eval_target_place_toplevel >> strip_tac >>
     first_x_assum irule >> simp[read_place_def] >> metis_tac[]) >>
  irule compile_augassign_toplevel_case_ptr >> simp[DISJ_IMP_THM] >>
  metis_tac[assignable_type_well_formed]
QED
