(* Memory case of the body induction, a widened aggregate internal call
   assigned to a place (bodyMemAssignOther's split): pure target indices,
   and e's lowered value has neither e's type nor a bytestring type e's
   fits, so e is an IntCall whose return type widens to the call's type.
   S1's twin is bodySimStmtCases' body_assign_place_widened_aggregate_call. *)
Theory bodyMemAssignPlaceWidened
Ancestors
  bodyMemoryPreds supportedTargets targetPlaceSim targetPlaceSimMem
  placeMemoryStagingMem typedCopyCounted

Theorem body_assign_place_widened_aggregate_call_mem:
  !cx t e d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' pv t'. eval_expr cx e s'' = (INL pv,t') ==>
                 body_base_target_mem_ok cx t) /\
    body_expr_mem_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget t) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget t) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget t) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget t) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget t) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
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
        type_place_target env t = SOME (Type fty) /\ is_word_type fty) /\
    ~immutable_root cx t /\
    supported_target_pure tops t /\
    ~(lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget t) e))
      (eval_stmt cx (Assign (BaseTarget t) e)) es

Proof
  cheat
QED
