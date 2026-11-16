(*
 * Augmented assignment over the finite-horizon joint judgment.
 * Stated over the finite-horizon full family (bodySimFull), one sub-shape
 * per S1 dispatch arm of bodySimStmtCases/bodySimDeclCases, so the case in
 * bodyFullCases closes by the same case split.
 *
 * TOP-LEVEL: the body_*_full sub-shape theorems below.
 *)
Theory bodyFullAugAssign
Ancestors
  augAssignStorageFieldSource
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  compileEnv exprLowering stmtLowering vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map augAssignFullToplevelCase augAssignPtrToplevelMetadata bodyStorageMetadata bodyExprPreFacts exprSimTopLevelProps stmtSimAugAssign supportedStmtTraverse supportedExprTraverse vyperTypeEnv vyperTypeInvariants gasContext vyperTypeCallGraph

val _ = Parse.hide "body";

(* A local. *)
Theorem body_augassign_local_full:
  !cx aty bop id e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (NameTarget id) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
    body_base_target_full_ok cx (NameTarget id) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign aty (NameTarget id) bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty (NameTarget id) bop e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign aty (NameTarget id) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign aty (NameTarget id) bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign aty (NameTarget id) bop e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty (NameTarget id) bop e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AugAssign aty (NameTarget id) bop e)))
      (eval_stmt cx (AugAssign aty (NameTarget id) bop e)) es
Proof
  cheat
QED

(* A scalar top-level variable. *)

Theorem body_augassign_toplevel_word_full:
  !cx aty bop nsid e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (TopLevelNameTarget nsid) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
    body_base_target_full_ok cx (TopLevelNameTarget nsid) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign aty (TopLevelNameTarget nsid) bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty (TopLevelNameTarget nsid) bop e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign aty (TopLevelNameTarget nsid) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign aty (TopLevelNameTarget nsid) bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign aty (TopLevelNameTarget nsid) bop e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    supported_scalar_target tops nsid ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty (TopLevelNameTarget nsid) bop e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AugAssign aty (TopLevelNameTarget nsid) bop e)))
      (eval_stmt cx (AugAssign aty (TopLevelNameTarget nsid) bop e)) es
Proof
  rpt gen_tac >> Cases_on `nsid` >> rename1 `TopLevelNameTarget (src,id)` >> strip_tac >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
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
  `type_place_target env (TopLevelNameTarget (NONE,id)) = SOME (Type aty) /\
   well_typed_expr env e /\ assignable_type env.type_defs aty /\
   well_typed_binop aty bop aty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
   (bop = Exp ==> nonneg_int_literal e) /\
   (bop = ShL ==> shift_amount_ok e) /\ (bop = ShR ==> shift_amount_ok e)` by
    (gvs[type_stmt_def, well_typed_target_def, DISJ_IMP_THM, AllCaseEqs()] >>
     metis_tac[stmtSimAugAssignTheory.augassign_operand_ok_operands]) >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all augassign_env_assignable_find_none >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  rename1 `find_var_decl_by_name id tops = SOME (StorageVarDecl tr _,_)` >>
  `dty = aty` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  `expr_body_pre cenv cx env e es` by
    (`cx_tops cx = tops` by metis_tac[cx_tops_module] >>
     `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
        is_dynamic (vyper_to_abi_type (type_env tops) target)` by fs[body_inv_def] >>
     irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supported_expr_exists_def, int_calls_stmt_def, int_calls_expr_def, optionTheory.IS_SOME_EXISTS] >>
     conj_tac >- metis_tac[body_inv_const_name_free] >>
     qexists_tac `[]` >> simp[]) >>
  irule compile_augassign_toplevel_case_full >> simp[DISJ_IMP_THM] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  qexists_tac `env` >> simp[] >> metis_tac[assignable_type_well_formed]
QED

(* A field of a struct local. *)
Theorem body_augassign_attr_local_full:
  !cx aty bop id fld e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (AttributeTarget (NameTarget id) fld) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
    body_base_target_full_ok cx (AttributeTarget (NameTarget id) fld) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e)))
      (eval_stmt cx (AugAssign aty (AttributeTarget (NameTarget id) fld) bop e)) es
Proof
  cheat
QED

(* A field of a storage struct. *)
Theorem body_augassign_attr_storage_full:
  !cx aty bop nsid fld e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (AttributeTarget (TopLevelNameTarget nsid) fld) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
    body_base_target_full_ok cx (AttributeTarget (TopLevelNameTarget nsid) fld) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    supported_storage_field_write tops nsid fld ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e)))
      (eval_stmt cx (AugAssign aty (AttributeTarget (TopLevelNameTarget nsid) fld) bop e)) es
Proof
  cheat
QED

(* Every other base target. *)
Theorem body_augassign_other_full:
  !cx aty bop t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_full_ok cx e) /\
    body_base_target_full_ok cx t /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign aty t bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign aty t bop e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign aty t bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign aty t bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign aty t bop e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~(?id. t = NameTarget id) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\
             supported_scalar_target tops nsid) /\
    ~(?id fld. t = AttributeTarget (NameTarget id) fld) /\
    ~(?nsid fld. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
                 supported_storage_field_write tops nsid fld) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign aty t bop e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (AugAssign aty t bop e)))
      (eval_stmt cx (AugAssign aty t bop e)) es
Proof
  cheat
QED
