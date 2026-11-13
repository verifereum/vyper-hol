Theory bodyPtrAugAssignLocal
Ancestors
  bodyPtrAugAssignLocalPrefix augAssignPtrMemoryOutcome
  bodyPtrPreds bodyPtrDefs bodyAugAssignOther

Theorem body_augassign_local_place_ptr:
  !d PG cx ty t bop e tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s0 p s1 s2 cur s3 s4 ptv s5.
       eval_target_place cx t s0 = (INL p,s1) /\
       read_place cx p s2 = (INL cur,s3) /\
       place_type_value cx p s4 = (INL ptv,s5) ==> body_expr_ptr_ok cx e) /\
    body_base_target_ptr_ok cx t /\ body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign ty t bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign ty t bop e) ==> occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
    body_stmt_safe tops (AugAssign ty t bop e) /\
    stmt_exprs_ok cenv (AugAssign ty t bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) /\
    frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty /\
    ~(?id. t = NameTarget id) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\ supported_scalar_target tops nsid) /\
    ~(?id fld. t = AttributeTarget (NameTarget id) fld) /\
    ~(?nsid fld. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
                 supported_storage_field_write tops nsid fld) /\
    ((?b fld. t = AttributeTarget b fld) \/ (?b k. t = SubscriptTarget b k)) /\
    (?id. target_root t = NameTarget id) /\
    (!id. target_root t = NameTarget id ==> local_target_live cx id t) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty t bop e))
      (eval_stmt cx (AugAssign ty t bop e)) es
Proof
  MATCH_ACCEPT_TAC body_augassign_local_place_from_suffix_ptr
QED
