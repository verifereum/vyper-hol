(* Linked compatible and bytestring local-memory copy route. *)
Theory bodyAssignNameCopyRouteMods
Ancestors
  bodyAssignNameLinkedSetup bodyFullPredsMods bodyFullPostsMods bodyWriteOperandMods
  bodyFullAssignMemoryCompose bodyLocalTypedCopyPathMods bodyLocalCopyWritesMods
  bodyLocalSnapshotResourcesMods bodyCopySlotRhsRunMods bodyCopyEqualRhsTypeMods
  assignBasePtrLocalBodyFacts bodyInvCodeProps bodyInvModuleProps bodyInvExecutionProps
  bodyInvMetadataProps bodyFullAssign bodySim
  gasShadowCompileStmtHelpers gasShadowState gasShadow compileEnv
  typedMemoryCopy valueEncodingProps exprBodyPreProps exprSimHypsDefs
  finite_map list pair words arithmetic

Theorem assign_name_copy_route_mods:
  linked_assign_name_context_mods mods exps cx id e
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    src tops bindings cenv env env' ret_ty RetQ es /\
  body_expr_full_ok_mods mods exps cx e /\
  FLOOKUP env.var_types id = SOME ty /\
  ~is_word_type ty /\
  0 < type_memory_bytes cenv ty /\
  (lowered_value_type cenv e = ty \/ is_bytestring_type ty) /\
  (lowered_value_type cenv e = expr_type e \/
   is_bytestring_type ty /\
   is_bytestring_type (lowered_value_type cenv e) /\
   arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) ==>
  stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty
      (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)))
    (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  cheat
QED
