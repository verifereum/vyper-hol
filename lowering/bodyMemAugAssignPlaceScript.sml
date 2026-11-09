(* Memory case of the body induction, augmented assignment
   (bodyMemAugAssignOther's split, as bodyAugAssignOther's
   body_augassign_other_leaf for S1), every target but a storage or
   transient place with an effectful index: a word storage or transient
   variable of any width, an immutable, a field or element of a local, and
   a field or element of a storage or transient variable with pure
   indices.  S1's twins: body_augassign_toplevel_aug,
   immutable_deploy_augassign_case, compile_augassign_place_memory_case,
   compile_augassign_place_storage_case. *)
Theory bodyMemAugAssignPlace
Ancestors
  bodyMemoryPreds supportedTargets targetPlaceSim targetPlaceSimMem
  augAssignPlaceMemoryTarget augAssignPlaceMemoryContinuation
  augAssignPlaceSuffixMemory augAssignPlaceRhsContinuation augAssignPlaceTopMemory
  augAssignPlaceCompileMemory

Theorem body_augassign_place_mem_case:
  !cx ty t bop e d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_mem_ok cx e) /\
    body_base_target_mem_ok cx t /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (AugAssign ty t bop e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AugAssign ty t bop e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty t bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    ~(?id. t = NameTarget id) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\
             supported_scalar_target tops nsid) /\
    ~(?id fld. t = AttributeTarget (NameTarget id) fld) /\
    ~(?nsid fld. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
                 supported_storage_field_write tops nsid fld) /\
    ~immutable_root cx t /\
    ~(~supported_target_pure tops t /\
     ~(?id. target_root t = NameTarget id)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty t bop e))
      (eval_stmt cx (AugAssign ty t bop e)) es

Proof
  cheat
QED
