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
  augAssignPlaceCompileMemory augAssignPlaceLoadContinuation
  augAssignPlaceSourceMemory augAssignPlaceCompositeMemory

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
  rpt strip_tac >>
  `supported_expr tops e` by fs[supportedStmtsTheory.supported_stmt_def] >>
  drule_all bodyAugAssignOtherTheory.augassign_rhs_pre >> strip_tac >>
  Cases_on `t`
  >- gvs[]
  >- (rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
      Cases_on `supported_aug_target tops bindings (TopLevelNameTarget (nsid0,nsid1))`
      >- (irule aug_place_toplevel_mem >> metis_tac[]) >>
      `?ity. supported_immutable_type tops (nsid0,nsid1) = SOME ity` by
        gvs[supportedStmtsTheory.supported_stmt_def,
            supportedStmtsTheory.supported_target_def, optionTheory.IS_SOME_EXISTS] >>
      gvs[supportedDeclsTheory.supported_immutable_type_def, AllCaseEqs()] >>
      drule bodyStorageMetadataTheory.supported_variable_decl_mem >> strip_tac >> gvs[] >>
      `get_module_code cx NONE = SOME tops /\
       ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
        fs[bodySimTheory.body_inv_def] >>
      drule_all vyperTypeContractStaticMapsTheory.find_var_decl_by_name_NONE_Immutable >>
      strip_tac >> fs[targetPlaceSimTheory.immutable_root_def,
                      targetPlaceSimTheory.target_root_def]) >>
  (qmatch_goalsub_abbrev_tac `AugAssign ty bt bop e` >>
   `((?b fld. bt = AttributeTarget b fld) \/ (?b k. bt = SubscriptTarget b k))` by
     simp[Abbr `bt`] >>
   `target_indices_pre cenv cx env bt` by
     metis_tac[bodyAugAssignOtherTheory.augassign_target_pre] >>
   `target_sim_mem ctx func cenv cx env bt es` by
     (irule body_target_sim_mem >>
      simp[targetPlaceSimTheory.target_pre_def] >> metis_tac[]) >>
   (Cases_on `?id. target_root bt = NameTarget id`
    >- (irule compile_augassign_place_memory_mem_case >> metis_tac[]) >>
    irule compile_augassign_place_storage_mem_case >> gvs[] >> metis_tac[]))
QED
