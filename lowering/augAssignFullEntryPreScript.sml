(* Source-side preconditions for finite-horizon AugAssign composition. *)
Theory augAssignFullEntryPre
Ancestors bodySingletonCallSupport vyperTypeEnv compileEnv targetPlaceSimCasesBase
  bodyAugPlaceTarget bodyExprPreFacts bodyStorageCases stmtSimAugAssignPlace stmtSimAugAssignPlaceMemory
  bodySim exprSimHypsDefs targetPlaceSim targetPlaceLive gasContext
  supportedStmts supportedTargets supportedExprTraverse supportedStmtTraverse
  allocLimits allocLimitsProps exprLowering vyperTypeSystem vyperTypeCallGraph
  vyperTypeCallStackSoundness vyperAST list bodyInvExecutionProps
  stmtExprAllocationPreProps compileUnit alist

Theorem augassign_entry_rhs_pre:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty t bop e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (AugAssign ty t bop e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign ty t bop e) /\
  call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) ==>
  expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  mp_tac (Q.INST [`tops` |-> `tops`, `ctx` |-> `ctx`,
                   `s` |-> `AugAssign ty t bop e`]
    body_inv_stmt_expr_pre_singleton) >>
  simp[supported_stmt_expr_exists_def] >>
  disch_then irule >>
  mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `exps` |-> `[]`,
                   `ctx` |-> `ctx`, `ty` |-> `ty`, `t` |-> `t`,
                   `bop` |-> `bop`, `bindings` |-> `bindings`,
                   `ret_ty` |-> `ret_ty`, `env'` |-> `env'`]
    augassign_entry_rhs_pre_mods) >>
  simp[main_module_def, ALOOKUP_def]
QED

Theorem typed_nested_immutable_root_nonword:
  !t vt env id root_ty.
    type_place_target env t = SOME vt /\
    target_root t = TopLevelNameTarget (NONE,id) /\
    t <> TopLevelNameTarget (NONE,id) /\
    FLOOKUP env.bare_global_assignable (NONE,id) = SOME root_ty ==>
    ~is_word_type root_ty
Proof
  ho_match_mp_tac base_assignment_target_induct >>
  simp[target_root_def,type_place_target_SubscriptTarget,type_place_target_AttributeTarget] >>
  rpt strip_tac >>
  Cases_on `t = TopLevelNameTarget (NONE,id)`
  >- (gvs[type_place_target_TopLevelNameTarget] >>
      Cases_on `root_ty` >> gvs[subscript_vtype_def,is_word_type_def])
  >- metis_tac[]
  >- (gvs[type_place_target_TopLevelNameTarget] >>
      Cases_on `root_ty` >> gvs[attribute_type_def,is_word_type_def]) >>
  metis_tac[]
QED

Theorem augassign_entry_target_indices_pre:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty t bop e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (AugAssign ty t bop e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign ty t bop e) /\
  call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) ==>
  target_indices_pre cenv cx env t
Proof
  strip_tac >>
  `call_evaluation_safe cx (int_calls_target t)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_stmt (AugAssign _ _ _ _))`
      (ACCEPT_TAC o MATCH_MP call_evaluation_safe_append_left o
       PURE_REWRITE_RULE [int_calls_stmt_def])) >>
  Cases_on `(?bt fld. t = AttributeTarget bt fld) \/
            (?bt k. t = SubscriptTarget bt k)`
  >- (
    `?pt. supported_target_info tops bindings t = SOME pt` by
      metis_tac[aug_place_supported_stmt_target_info] >>
    drule (cj 1 aug_place_typing) >> strip_tac >>
    `supported_program tops /\ get_module_code cx NONE = SOME tops /\
     (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
       is_dynamic (vyper_to_abi_type (type_env tops) target))` by
      metis_tac[body_inv_main_support, body_inv_singleton_abi_types] >>
    `alloc_limits_target cenv t` by
      fs[stmt_exprs_ok_def, alloc_limits_stmt_def] >>
    `EVERY (\e. ~is_extcode e) (target_indices t)` by
      metis_tac[alloc_limits_target_indices_not_extcode] >>
    `IS_SOME (type_place_target env t)` by simp[] >>
    drule_all_then assume_tac body_inv_typed_target_calls_main >>
    mp_tac (Q.SPECL [`tops`, `bindings`, `t`] supported_target_info_main_calls) >>
    simp[] >> strip_tac >>
    `~supported_target_exists (const_name_root cx) t` by
      (drule_all body_inv_stmt_const_name_free >>
       simp[supported_stmt_expr_exists_def]) >>
    irule (Q.INST [`tops` |-> `tops`, `bindings` |-> `bindings`]
      aug_place_target_indices_pre) >>
    gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
        alloc_limits_stmt_def, int_calls_stmt_def] >>
    simp[optionTheory.IS_SOME_EXISTS] >>
    fs[EVERY_MEM] >> qexists_tac `bindings` >> conj_tac
    >- (qexists_tac `pt` >> simp[]) >>
    rpt strip_tac >> res_tac >> fs[optionTheory.IS_SOME_EXISTS]) >>
  Cases_on `t` >> gvs[target_indices_pre_def]
QED

Theorem augassign_entry_target_pre:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty t bop e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (AugAssign ty t bop e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign ty t bop e) /\
  call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) /\
  ~immutable_root cx t ==>
  target_pre cenv cx env t es
Proof
  strip_tac >> simp[target_pre_def] >>
  drule_all augassign_entry_target_indices_pre >> simp[]
QED
