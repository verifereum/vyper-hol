(*
 * Tuple assignment over the finite-horizon joint judgment.
 * Stated over the finite-horizon full family (bodySimFull), one sub-shape
 * per S1 dispatch arm of bodySimStmtCases/bodySimDeclCases, so the case in
 * bodyFullCases closes by the same case split.
 *
 * TOP-LEVEL: the body_*_full sub-shape theorems below.
 *)
Theory bodyFullAssignTuple
Ancestors
  bodyFullPreds bodySimFull gasShadow bodySim exprSimHypsDefs supportedStmts
  compileEnv exprLowering stmtLowering vyperTypeSystem vyperContext
  vyperInterpreter vyperState vyperValue vyperAST list finite_map

val _ = Parse.hide "body";

(* A source that is a widened aggregate call. *)
Theorem body_assign_tuple_widened_full:
  !cx gs e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_full_ok cx (TupleTarget gs) v) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (TupleTarget gs) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    lowered_value_type cenv e <> expr_type e ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (TupleTarget gs) e)))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED

(* Every target a local. *)
Theorem body_assign_tuple_locals_full:
  !cx ids e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_full_ok cx (TupleTarget (MAP (BaseTarget o NameTarget) ids)) v) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    ids <> [] /\
    EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty /\
                     0 < type_memory_bytes cenv ty) ids /\
    lowered_value_type cenv e = expr_type e ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)))
      (eval_stmt cx (Assign (TupleTarget (MAP (BaseTarget o NameTarget) ids)) e)) es
Proof
  cheat
QED

(* Every target a local, a scalar top-level variable or a storage word field. *)
Theorem body_assign_tuple_targets_full:
  !cx gs e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_full_ok cx (TupleTarget gs) v) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (TupleTarget gs) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    lowered_value_type cenv e = expr_type e /\
    EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                        FLOOKUP env.var_types id = SOME ty /\
                        0 < type_memory_bytes cenv ty) \/
               (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
                       supported_scalar_target tops nsid) \/
               (?nsid fld fty.
                  g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                  supported_storage_field_write tops nsid fld /\
                  type_place_target env
                    (AttributeTarget (TopLevelNameTarget nsid) fld) =
                    SOME (Type fty) /\ is_word_type fty)) gs ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (TupleTarget gs) e)))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED

(* Any other target list. *)
Theorem body_assign_tuple_other_full:
  !cx gs e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_full_ok cx (TupleTarget gs) v) /\
    body_expr_full_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (TupleTarget gs) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
    lowered_value_type cenv e = expr_type e /\
    ~(?ids. gs = MAP (BaseTarget o NameTarget) ids /\ ids <> [] /\
            EVERY (\id. ?ty. FLOOKUP env.var_types id = SOME ty) ids) /\
    ~EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                        FLOOKUP env.var_types id = SOME ty /\
                        0 < type_memory_bytes cenv ty) \/
               (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
                       supported_scalar_target tops nsid) \/
               (?nsid fld fty.
                  g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                  supported_storage_field_write tops nsid fld /\
                  type_place_target env
                    (AttributeTarget (TopLevelNameTarget nsid) fld) =
                    SOME (Type fty) /\ is_word_type fty)) gs ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (stmt_env cenv lctx ret_ty (gas_shadow_stmt (Assign (TupleTarget gs) e)))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED
