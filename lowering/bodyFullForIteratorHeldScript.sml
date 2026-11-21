Theory bodyFullForIteratorHeld
Ancestors
  bodyFullForArrayBranch
  vyperTypeContract[qualified,ignore_grammar]

(* GATE_ADMISSION: missing case, array iterator through a nested storage or transient place; owner: body place lane *)
Theorem compile_for_storage_subplace_array_frag_full:
  !cx id typ e n body DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    ~(?bd nid. e = TopLevelName (ArrayT typ bd) nid /\
               supported_storage_value tops nid (ArrayT typ bd)) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx (Array e) s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_full_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_full_ok cx (Array e)) /\
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\ supported_stmt tops bindings (For id typ (Array e) n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ (Array e) n body) ==>
       occurs_abi_decode_target target tops) /\
    stmt_loop_calls_ok [(NONE,tops)] (For id typ (Array e) n body) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ (Array e) n body) = SOME env' /\
    ~supported_expr_exists (const_name_root cx) e /\
    stmt_exprs_ok cenv (For id typ (Array e) n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n body)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~(?ty nid. e = TopLevelName ty nid) /\
    (?tgt nid. loop_iterator_place e = SOME tgt /\
       target_root tgt = TopLevelNameTarget nid /\
       ((?vis kind ty slot.
          supported_variable_decl tops nid = SOME (vis,kind,ty,SOME slot) /\
          (kind = Storage \/ kind = Transient)) \/
        (?vis transient kt vt slot.
          supported_hashmap_decl tops nid = SOME (vis,transient,kt,vt,SOME slot)))) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ (Array e) n body))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n body)))
      (eval_stmt cx (For id typ (Array e) n body)) es
Proof
  cheat
QED

(* GATE_ADMISSION: missing case, array iterator through a nested immutable place; owner: body place lane *)
Theorem compile_for_immutable_subplace_array_frag_full:
  !cx id typ e n body DF lo d PG tops bindings ctx shadow_ctx func
   shadow_func cenv env env' ret_ty lctx RetQ es.
    ~(?bd nid. e = TopLevelName (ArrayT typ bd) nid /\
               supported_storage_value tops nid (ArrayT typ bd)) /\
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\ eval_iterator cx (Array e) s'3' = (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_full_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_full_ok cx (Array e)) /\
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\ supported_stmt tops bindings (For id typ (Array e) n body) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (For id typ (Array e) n body) ==>
       occurs_abi_decode_target target tops) /\
    stmt_loop_calls_ok [(NONE,tops)] (For id typ (Array e) n body) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (For id typ (Array e) n body) = SOME env' /\
    ~supported_expr_exists (const_name_root cx) e /\
    stmt_exprs_ok cenv (For id typ (Array e) n body) /\
    call_evaluation_safe cx (int_calls_stmt (For id typ (Array e) n body)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ~(?ty nid. e = TopLevelName ty nid) /\
    (?tgt nid. loop_iterator_place e = SOME tgt /\ target_root tgt = TopLevelNameTarget nid /\
       IS_SOME (supported_immutable_type tops nid)) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (For id typ (Array e) n body))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (For id typ (Array e) n body)))
      (eval_stmt cx (For id typ (Array e) n body)) es
Proof
  cheat
QED
