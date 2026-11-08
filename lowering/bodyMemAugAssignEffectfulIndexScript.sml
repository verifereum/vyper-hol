(* Memory case of the body induction, augmented assignment to a storage or
   transient place whose indices have effects (bodyMemAugAssignOther's
   split).  S1's twin is bodyAugAssignOther's
   augassign_place_effectful_index_case. *)
Theory bodyMemAugAssignEffectfulIndex
Ancestors
  bodyMemoryPreds supportedTargets targetPlaceSim

(* RESIDUAL (held): false on the frozen definitions, as its S1 twin: an
   index call in the target can replace the nested array the target names
   (checked counterexample nested_external_frozen_counterexample).  Waits on
   the target-overlap rejection (target_subscript_overlap in
   alloc_limits defs), the pop()-base overlap rejection and exact subscript
   base typing; not to be proved or launched before those land. *)
Theorem body_augassign_effectful_index_mem:
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
    (~supported_target_pure tops t /\
     ~(?id. target_root t = NameTarget id)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty t bop e))
      (eval_stmt cx (AugAssign ty t bop e)) es

Proof
  cheat
QED
