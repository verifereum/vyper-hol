(* Assignment fragments selected by the target at the actual entry. *)
Theory s1PrefixBoolChainSelectedFieldScalarAssign
Ancestors
  s1PrefixAssign s1PrefixDefs s1PrefixPreds bodyFullPreds bodySimFull
  stmtLowering gasShadow gasShadowCompileStmtBase vyperAST vyperInterpreter
  vyperTypeSystem vyperTypeEnv bodyStorageMetadata exprSimHypsDefs

Theorem bool_chain_selected_field_scalar_assign_prefix:
  !cx t e DF lo d PG tops bindings ctx shadow_ctx func shadow_func
      cenv env env' ret_ty lctx RetQ es.
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx t) /\
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_prefix_ok cx t) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Assign (BaseTarget t) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget t) e) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
  ((?nsid dty. t = TopLevelNameTarget nsid /\
               supported_scalar_target tops nsid /\
               type_place_target env t = SOME (Type dty) /\ is_word_type dty) \/
   (?id fld sid fty. t = AttributeTarget (NameTarget id) fld /\
                    FLOOKUP env.var_types id = SOME (StructT sid) /\
                    attribute_type env.type_defs (StructT sid) fld = SOME fty /\
                    is_word_type fty) \/
   (?nsid fld fty. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
                  supported_storage_field_write tops nsid fld /\
                  type_place_target env t = SOME (Type fty) /\ is_word_type fty)) ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty
        (gas_shadow_stmt (Assign (BaseTarget t) e)))
      (eval_stmt cx (Assign (BaseTarget t) e)) es
Proof
  rpt gen_tac >> strip_tac
  >- (gvs[] >> irule body_assign_toplevel_word_prefix >> metis_tac[])
  >- (gvs[] >> irule body_assign_attr_local_prefix >> metis_tac[])
  >> gvs[] >> irule body_assign_attr_storage_prefix >> metis_tac[]
QED
