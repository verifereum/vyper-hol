(*
 * Assignment to a base target over the finite-horizon joint judgment.
 * Stated over the finite-horizon full family (bodySimFull), one sub-shape
 * per S1 dispatch arm of bodySimStmtCases/bodySimDeclCases, so the case in
 * bodyFullCases closes by the same case split.
 *
 * TOP-LEVEL: the body_*_full sub-shape theorems below.
 *)
Theory bodyFullAssign
Ancestors
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  compileEnv exprLowering stmtLowering vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map
  bodyFullAssignAttrStorage bodyExprPreFacts bodyStorageMetadata
  bodyFullMemoryFrames bodyFullMemoryCopy bodyFullMemoryStore
  stmtSimAssignAttr exprSimFieldLayout exprSimHyps exprSimSource
  supportedExprForms supportedExprs supportedExprTraverse supportedStmtTraverse
  vyperTypeEnv vyperTypeInvariants vyperTypeContractStaticMaps
  compileVyper supportedDecls gasContext vyperTypeCallGraph

val _ = Parse.hide "body";

(* A word local. *)
Theorem body_assign_local_word_full:
  !cx id ty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (NameTarget id)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME ty /\
    is_word_type ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  cheat
QED

(* A memory local whose source is stored at its own layout. *)
Theorem body_assign_local_memory_full:
  !cx id ty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (NameTarget id)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME ty /\
    ~is_word_type ty /\
    0 < type_memory_bytes cenv ty /\
    (lowered_value_type cenv e = ty \/ is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  cheat
QED

(* A memory local whose source is a widened aggregate. *)
Theorem body_assign_local_widened_full:
  !cx id ty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (NameTarget id)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME ty /\
    ~is_word_type ty /\
    0 < type_memory_bytes cenv ty /\
    (expr_type e = ty \/ lowered_value_type cenv e = ty \/ is_bytestring_type ty \/
     has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    ~(lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  cheat
QED

(* A scalar top-level variable. *)
Theorem body_assign_toplevel_word_full:
  !cx nsid e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (TopLevelNameTarget nsid)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (TopLevelNameTarget nsid)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    supported_scalar_target tops nsid ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) es
Proof
  cheat
QED

(* A static aggregate storage or transient variable. *)
Theorem body_assign_toplevel_copy_full:
  !cx nsid mut ty slot e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (TopLevelNameTarget nsid)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (TopLevelNameTarget nsid)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nsid)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~supported_scalar_target tops nsid /\
    supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
    (mut = Storage \/ mut = Transient) /\
    ~is_word_type ty /\
    (!elem n. ty <> ArrayT elem (Dynamic n)) /\
    0 < type_memory_bytes cenv ty /\
    expr_type e = ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (TopLevelNameTarget nsid)) e)))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) es
Proof
  cheat
QED

(* A word field of a memory struct local. *)
Theorem body_assign_attr_local_full:
  !cx id fld sid fty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (AttributeTarget (NameTarget id) fld)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    FLOOKUP env.var_types id = SOME (StructT sid) /\
    attribute_type env.type_defs (StructT sid) fld = SOME fty /\
    is_word_type fty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (NameTarget id) fld)) e)) es
Proof
  cheat
QED

(* A word field of a storage struct. *)
Theorem body_assign_attr_storage_full:
  !cx nsid fld fty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (AttributeTarget (TopLevelNameTarget nsid) fld)) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    supported_storage_field_write tops nsid fld /\
    type_place_target env (AttributeTarget (TopLevelNameTarget nsid) fld) =
      SOME (Type fty) /\
    is_word_type fty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e)))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e)) es
Proof
  rpt gen_tac >> strip_tac >> PairCases_on `nsid` >>
  rename1 `supported_storage_field_write tops (src,id) fld` >>
  `well_typed_expr env e /\ expr_type e = fty` by
    (gvs[type_stmt_def, atarget_accepts_def] >> metis_tac[type_widens_to_word]) >>
  `src = NONE /\ find_var_decl_by_name id tops <> NONE /\
   ?vis mut sid slot. MEM (VariableDecl vis mut id (StructT sid) slot) tops` by
    (drule supported_storage_field_write_decl >> simp[]) >>
  gvs[] >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)` by
    fs[body_inv_def] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  gvs[type_place_target_AttributeTarget, type_place_target_TopLevelNameTarget]
  >- (`?ts. get_module_code cx NONE = SOME ts /\
              find_var_decl_by_name id ts = NONE` by
        (fs[env_consistent_def, env_context_consistent_def] >>
         first_x_assum drule >> strip_tac >>
         metis_tac[optionTheory.SOME_11]) >>
      metis_tac[optionTheory.SOME_11]) >>
  drule_all env_consistent_toplevel_storage_static >> strip_tac >>
  drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  rename1 `attribute_type _ tgt_ty fld = SOME _` >>
  `tgt_ty = StructT sid` by
    metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >> drule_all build_maps_variable >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  `?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
              fld = SOME (expr_type e,fsz)` by
    metis_tac[attribute_type_struct_field] >>
  `supported_expr tops e` by
    fs[supported_stmt_def, supported_assignment_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supported_assignment_exists_def, supported_expr_exists_def,
         int_calls_stmt_def, int_calls_atarget_def, int_calls_expr_def,
         body_inv_def] >> qexists_tac `[]` >> simp[]) >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_assum `body_expr_full_ok _ _`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [body_expr_full_ok_def]) >>
     disch_then (qspecl_then [`DF`, `lo`, `d`, `PG`, `tops`, `ctx`,
       `shadow_ctx`, `func`, `shadow_func`, `cenv`, `env`, `expr_type e`, `es`]
       mp_tac) >> simp[]) >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  irule compile_assign_attr_storage_full >> simp[] >> metis_tac[]
QED

(* Every other base target: subscripts, nested attributes, immutables. *)
Theorem body_assign_other_full:
  !cx t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx t) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (BaseTarget t) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget t) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              is_word_type ty) /\
    ~(?id ty. t = NameTarget id /\ FLOOKUP env.var_types id = SOME ty /\
              ~is_word_type ty /\
              (expr_type e = ty \/ lowered_value_type cenv e = ty \/
               is_bytestring_type ty \/
               has_length_word (expr_type e) /\ is_empty_value_expr e)) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\ supported_scalar_target tops nsid) /\
    ~(?nsid mut ty slot.
        t = TopLevelNameTarget nsid /\
        supported_variable_decl tops nsid = SOME (Private, mut, ty, SOME slot) /\
        (mut = Storage \/ mut = Transient) /\
        ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
        0 < type_memory_bytes cenv ty /\ expr_type e = ty) /\
    ~(?id fld sid fty.
        t = AttributeTarget (NameTarget id) fld /\
        FLOOKUP env.var_types id = SOME (StructT sid) /\
        attribute_type env.type_defs (StructT sid) fld = SOME fty /\
        is_word_type fty) /\
    ~(?nsid fld fty.
        t = AttributeTarget (TopLevelNameTarget nsid) fld /\
        supported_storage_field_write tops nsid fld /\
        type_place_target env t = SOME (Type fty) /\ is_word_type fty) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (BaseTarget t) e)))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  cheat
QED
