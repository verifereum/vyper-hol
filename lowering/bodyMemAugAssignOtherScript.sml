(* Memory case of the body induction, augmented assignment
   (bodyMemAugAssign's dispatch): every target the other subcases leave
   (S1's body_augassign_other, itself admitted there): storage struct
   fields outside supported_storage_field_write, immutables, nested
   attributes and subscripts. *)
Theory bodyMemAugAssignOther
Ancestors
  bodyMemoryPreds bodyMemImmutableDeploy bodyMemAugAssignPlace bodyMemAugAssignEffectfulIndex

Theorem body_augassign_other_mem:
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
                 supported_storage_field_write tops nsid fld) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty t bop e))
      (eval_stmt cx (AugAssign ty t bop e)) es
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `immutable_root cx t`
  >- (qspecl_then [`cx`,`ty`,`t`,`bop`,`e`,`d`,`tops`,`bindings`,`ctx`,`func`,`cenv`,`env`,`env'`,`ret_ty`,`lctx`,`RetQ`,`es`] mp_tac body_augassign_immutable_deploy_mem >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
  Cases_on `(~supported_target_pure tops t /\
            ~(?id. target_root t = NameTarget id))`
  >- (pop_assum strip_assume_tac >>
      qspecl_then [`cx`,`ty`,`t`,`bop`,`e`,`d`,`tops`,`bindings`,`ctx`,`func`,`cenv`,`env`,`env'`,`ret_ty`,`lctx`,`RetQ`,`es`] mp_tac body_augassign_effectful_index_mem >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
  (qspecl_then [`cx`,`ty`,`t`,`bop`,`e`,`d`,`tops`,`bindings`,`ctx`,`func`,`cenv`,`env`,`env'`,`ret_ty`,`lctx`,`RetQ`,`es`] mp_tac body_augassign_place_mem_case >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC)
QED
