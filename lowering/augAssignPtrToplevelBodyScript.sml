(* Body-level storage/transient scalar target dispatch. *)
Theory augAssignPtrToplevelBody
Ancestors
  augAssignPtrToplevelCase augAssignPtrToplevelMetadata bodyStorageMetadata
  bodyExprPreFacts bodyPtrPreds bodyPtrDefs bodySim supportedStmts
  exprSimHypsDefs exprSimTopLevelProps stmtSimAugAssignStorage
  vyperTypeEnv vyperTypeInvariants vyperTypeSystem vyperTyping
  vyperState vyperInterpreter vyperTypeCallGraph supportedStmtTraverse
  supportedExprTraverse gasContext compileVyper compileEnv list finite_map

Theorem augassign_toplevel_rhs_activate_ptr[local]:
  (!s0 p s1 s2 cur s3 s4 ptv s5.
     eval_target_place cx (TopLevelNameTarget (src,id)) s0 = (INL p,s1) /\
     read_place cx p s2 = (INL cur,s3) /\
     place_type_value cx p s4 = (INL ptv,s5) ==> body_expr_ptr_ok cx e) /\
  expr_body_pre cenv cx env e es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) ty = SOME tvt ==>
  body_expr_ptr_ok cx e
Proof
  strip_tac >>
  `?v. read_storage_slot cx tr (n2w slot) tvt es = (INL v,es)` by
    (irule toplevel_storage_read_decodes >> fs[expr_body_pre_def, expr_sim_inv_def] >>
     metis_tac[]) >>
  drule_all eval_target_place_toplevel >> strip_tac >>
  first_x_assum irule >> simp[read_place_def] >> metis_tac[]
QED

Theorem body_augassign_toplevel_word_ptr:
  !cx ty src id bop e tops ctx PG func cenv env env' ret_ty lctx RetQ es.
    (!s0 p s1 s2 cur s3 s4 ptv s5.
       eval_target_place cx (TopLevelNameTarget (src,id)) s0 = (INL p,s1) /\
       read_place cx p s2 = (INL cur,s3) /\
       place_type_value cx p s4 = (INL ptv,s5) ==> body_expr_ptr_ok cx e) /\
    body_inv tops ctx cenv cx /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign ty (TopLevelNameTarget (src,id)) bop e) ==>
       occurs_abi_decode_target target tops) /\
    supported_scalar_target tops (src,id) /\ supported_expr tops e /\
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
  drule augassign_supported_scalar_target_decl >> strip_tac >> gvs[] >>
  rename1 `MEM (VariableDecl vis mut id dty init) tops` >>
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
    gvs[type_stmt_def, well_typed_target_def, DISJ_IMP_THM, AllCaseEqs()] >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all augassign_env_assignable_find_none >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  rename1 `find_var_decl_by_name id tops = SOME (StorageVarDecl tr _,_)` >>
  `dty = ty` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `lookup_var_slot_from_layout _ _ _ _ = SOME slot` >>
  rename1 `evaluate_type _ ty = SOME tvt` >>
  suspend "finish"
QED

Resume body_augassign_toplevel_word_ptr[finish]:
  `expr_body_pre cenv cx env e es` by
    (`cx_tops cx = tops` by metis_tac[cx_tops_module] >>
     `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
        is_dynamic (vyper_to_abi_type (type_env tops) target)` by fs[body_inv_def] >>
     irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def, optionTheory.IS_SOME_EXISTS] >>
     qexists_tac `[]` >> simp[]) >>
  drule_all augassign_toplevel_rhs_activate_ptr >> disch_tac >>
  irule compile_augassign_toplevel_case_ptr >> simp[DISJ_IMP_THM] >>
  conj_tac >- (qexists_tac `tops` >> simp[]) >>
  qexists_tac `env` >> simp[] >>
  metis_tac[assignable_type_well_formed]
QED

Finalise body_augassign_toplevel_word_ptr
