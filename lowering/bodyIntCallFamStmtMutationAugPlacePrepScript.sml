(* Entry preparation for mutable nonlocal augmented assignments. *)
Theory bodyIntCallFamStmtMutationAugPlacePrep
Ancestors
  bodyAugPlaceTarget bodyAugAssignOther bodyExprPreFacts
  supportedStmts supportedTargets supportedExprForms supportedTypes
  vyperTypeSystem vyperTypeEnv targetPlaceSim bodySim
  supportedDecls vyperTypeInvariants exprSimHypsDefs bodyStorageMetadata
  supportedStmtTraverse vyperTypeCallGraph

Theorem intcall_scalar_target_info:
  supported_scalar_target tops nsid ==>
  IS_SOME (supported_target_info tops bindings (TopLevelNameTarget nsid))
Proof
  simp[supported_scalar_target_def, supported_target_info_def,
       supported_place_root_def] >>
  Cases_on `supported_variable_decl tops nsid` >> simp[] >>
  rename1 `SOME decl` >> PairCases_on `decl` >>
  Cases_on `decl0` >> Cases_on `decl1` >> Cases_on `decl3` >>
  simp[] >> strip_tac >>
  `supported_storage_type tops decl2` by
    simp[supported_storage_type_def,Once supported_nested_type_def] >>
  simp[] >> Cases_on `supported_hashmap_decl tops nsid` >> simp[] >>
  rename1 `SOME h` >> PairCases_on `h` >> simp[]
QED

Theorem intcall_mutable_toplevel_not_supported_immutable:
  expr_sim_inv ce cx env es /\ get_module_code cx NONE = SOME tops /\
  target_mutable env (TopLevelNameTarget nsid) ==>
  supported_immutable_type tops nsid = NONE
Proof
  strip_tac >> PairCases_on `nsid` >>
  Cases_on `supported_immutable_type tops (nsid0,nsid1)` >> simp[] >>
  fs[supported_immutable_type_def,AllCaseEqs()] >>
  drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  fs[target_mutable_def,expr_sim_inv_def,env_consistent_def,
     env_context_consistent_def,bare_globals_complete_def] >>
  metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem intcall_aug_place_entry_ready:
  body_inv tops ctx ce cx /\
  supported_stmt tops bindings (AugAssign ty tg bop rhs) /\
  type_stmt env ret_ty (AugAssign ty tg bop rhs) = SOME env' /\
  expr_sim_inv ce cx env es /\ stmt_exprs_ok ce (AugAssign ty tg bop rhs) /\
  (!id. tg <> NameTarget id) /\
  call_evaluation_safe cx (int_calls_stmt (AugAssign ty tg bop rhs)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (AugAssign ty tg bop rhs) ==> occurs_abi_decode_target target tops) ==>
  target_indices_pre ce cx env tg /\ target_pre ce cx env tg es /\
  (?info. supported_target_info tops bindings tg = SOME info)
Proof
  strip_tac >>
  `body_stmt_safe tops (AugAssign ty tg bop rhs)` by
    metis_tac[supported_stmt_body_safe] >>
  (Cases_on `?nsid. tg = TopLevelNameTarget nsid` >- suspend "toplevel") >>
  (Q.SUBGOAL_THEN
    `(?bt fld. tg = AttributeTarget bt fld) \/ (?bt key. tg = SubscriptTarget bt key)`
    assume_tac >- (Cases_on `tg` >> gvs[])) >>
  `target_indices_pre ce cx env tg` by metis_tac[augassign_target_pre] >>
  `?info. supported_target_info tops bindings tg = SOME info` by
    metis_tac[aug_place_supported_stmt_target_info] >>
  metis_tac[target_pre_def,aug_place_supported_root_not_immutable]
QED

Resume intcall_aug_place_entry_ready[toplevel]:
  gvs[] >>
  `target_mutable env (TopLevelNameTarget nsid)` by
    fs[vyperTypeSystemTheory.type_stmt_def,AllCaseEqs()] >>
  `get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  drule_all intcall_mutable_toplevel_not_supported_immutable >> strip_tac >>
  `IS_SOME (supported_target_info tops bindings (TopLevelNameTarget nsid))` by
    (fs[supported_stmt_def,supported_target_def]
     >- (irule intcall_scalar_target_info >> simp[]) >>
     Cases_on `supported_target_info tops bindings (TopLevelNameTarget nsid)` >>
     gvs[supported_aug_target_def] >> rename1 `SOME pt` >>
     Cases_on `pt` >> gvs[]) >>
  fs[optionTheory.IS_SOME_EXISTS] >>
  simp[target_indices_pre_def,target_pre_def] >>
  metis_tac[aug_place_supported_root_not_immutable]
QED

Finalise intcall_aug_place_entry_ready
