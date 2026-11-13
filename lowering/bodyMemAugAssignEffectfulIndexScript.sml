(* Memory case of the body induction, augmented assignment to a storage or
   transient place whose indices have effects (bodyMemAugAssignOther's
   split).  S1's twin is bodyAugAssignOther's
   augassign_place_effectful_index_case. *)
Theory bodyMemAugAssignEffectfulIndex
Ancestors
  bodyMemoryPreds supportedTargets targetPlaceSim targetPlaceSimMem
  augAssignPlaceEffectfulMemory bodyAugAssignOther
Theorem body_augassign_effectful_index_mem:
  !cx ty t bop e d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_mem_ok cx e) /\
    body_base_target_mem_ok cx t /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (AugAssign ty t bop e) /\
    body_stmt_safe tops (AugAssign ty t bop e) /\
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
  rpt strip_tac >>
  `supported_expr tops e` by fs[supportedStmtsTheory.supported_stmt_def] >>
  drule_all bodyAugAssignOtherTheory.augassign_rhs_pre >> strip_tac >>
  Cases_on `t`
  >- gvs[]
  >- (gvs[supportedStmtsTheory.supported_stmt_def,
          supportedStmtsTheory.supported_target_def,
          supportedTargetsTheory.supported_target_pure_def]) >>
  (qmatch_goalsub_abbrev_tac `AugAssign ty bt bop e` >>
   `((?b fld. bt = AttributeTarget b fld) \/ (?b k. bt = SubscriptTarget b k))` by
     simp[Abbr `bt`] >>
   `target_indices_pre cenv cx env bt` by
     metis_tac[bodyAugAssignOtherTheory.augassign_target_pre] >>
   `?pt. supported_target_info tops bindings bt = SOME pt` by
     metis_tac[bodyAugPlaceTargetTheory.aug_place_supported_stmt_target_info] >>
   `~immutable_root cx bt` by
     metis_tac[bodyAugPlaceTargetTheory.aug_place_supported_root_not_immutable] >>
   `EVERY (supported_expr tops) (target_indices bt)` by
     (`IS_SOME (supported_target_info tops bindings bt)` by simp[] >>
      drule bodyAugPlaceTargetTheory.aug_place_supported_indices >>
      strip_tac >> simp[listTheory.EVERY_MEM] >> first_assum ACCEPT_TAC) >>
   `target_sim_mem ctx func cenv cx env bt es` by
     (irule body_target_sim_mem >>
      simp[targetPlaceSimTheory.target_pre_def] >> metis_tac[]) >>
   irule compile_augassign_place_effectful_storage_mem_case >> gvs[] >> metis_tac[])
QED
