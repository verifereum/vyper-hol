(* Static preparation shared by both BaseTarget Assign compiler paths. *)
Theory bodyIntCallFamStmtMutationAssignBaseEntry
Ancestors
  bodyIntCallJointContract bodyExprPreFacts bodyAugPlaceTarget
  bodyIntCallFamStmtMutationAugPlacePrep popTargetPre
  supportedStmtTraverse supportedStmts supportedTargets supportedExprForms supportedTypes
  vyperTypeSystem vyperTypeCallStackSoundness exprSimHypsDefs bodySim
  stmtLowering allocLimits targetPlaceLive vyperTypeInvariants
  gasContext vyperTypeCallGraph supportedExprTraverse

Theorem intcall_assign_supported_value_place:
  !tops ty. supported_value_type tops ty ==> supported_place_type tops ty
Proof
  `!fuel tops ty. supported_scalar_type ty ==>
    supported_nested_type supported_scalar_type fuel tops ty` by
    (rpt gen_tac >> simp[Once supported_nested_type_def]) >>
  rpt gen_tac >>
  rewrite_tac[supported_value_type_def,supported_place_type_def] >>
  disch_then DISJ_CASES_TAC >- metis_tac[] >>
  Cases_on `ty` >> gvs[]
  >- (simp[Once supported_nested_type_def] >>
      disj2_tac >> simp[listTheory.EVERY_MEM] >>
      fs[listTheory.EVERY_MEM] >> metis_tac[])
  >- (Cases_on `b` >> gvs[] >>
      simp[Once supported_nested_type_def] >>
      metis_tac[supported_scalar_type_def]) >>
  gvs[AllCaseEqs()] >>
  `tops <> []` by (strip_tac >> gvs[supported_struct_fields_def]) >>
  simp[Once supported_nested_type_def] >>
  disj2_tac >> simp[] >>
  Cases_on `supported_struct_fields tops p` >> gvs[] >>
  fs[listTheory.EVERY_MEM] >>
  metis_tac[supported_scalar_type_def]
QED

Theorem intcall_assign_base_entry:
  body_inv tops ctx ce cx /\
  supported_stmts tops bindings [Assign (BaseTarget bt) rhs] /\
  (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target)
    [Assign (BaseTarget bt) rhs] ==> occurs_abi_decode_target target tops) /\
  type_stmts env ret_ty [Assign (BaseTarget bt) rhs] = SOME env' /\
  IS_SOME (type_stmts (env with bare_global_assignable := FEMPTY)
    ret_ty [Assign (BaseTarget bt) rhs]) /\
  stmts_exprs_ok ce [Assign (BaseTarget bt) rhs] /\
  call_evaluation_safe cx (int_calls_stmts [Assign (BaseTarget bt) rhs]) /\
  expr_sim_inv ce cx env es ==>
  env' = env /\ supported_expr tops rhs /\
  (?dty. type_place_target env bt = SOME (Type dty) /\
    type_widens_to env.type_defs (expr_type rhs) dty) /\
  assignable_type env.type_defs (expr_type rhs) /\
  IS_SOME (supported_target_info tops bindings bt) /\
  ~immutable_root cx bt /\ target_indices_pre ce cx env bt /\
  (!ee. expr_sim_inv ce cx env ee ==> expr_body_pre ce cx env rhs ee) /\
  (!target. supported_target_exists (expr_abi_decode_target_root target) bt ==>
    occurs_abi_decode_target target tops)
Proof
  strip_tac >>
  `type_stmt env ret_ty (Assign (BaseTarget bt) rhs) = SOME env'` by
    gvs[type_stmt_def,DISJ_IMP_THM,AllCaseEqs()] >>
  `supported_stmt tops bindings (Assign (BaseTarget bt) rhs)` by
    fs[supported_stmt_def] >>
  `body_stmt_safe tops (Assign (BaseTarget bt) rhs)` by
    metis_tac[supported_stmt_body_safe] >>
  `supported_expr tops rhs` by
    fs[supported_stmt_def,supported_assignment_def] >>
  `env' = env /\ well_typed_expr env rhs /\
   assignable_type env.type_defs (expr_type rhs) /\
   ?dty. type_place_target env bt = SOME (Type dty) /\
     type_widens_to env.type_defs (expr_type rhs) dty` by
    (gvs[type_stmt_def,atarget_accepts_def,AllCaseEqs()] >>
     Cases_on `type_place_target env bt` >> gvs[] >> Cases_on `x` >> gvs[]) >>
  `!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (Assign (BaseTarget bt) rhs) ==> occurs_abi_decode_target target tops` by
    (fs[supported_stmts_expr_exists_list] >> metis_tac[]) >>
  `IS_SOME (supported_target_info tops bindings bt)` by suspend "target_info" >>
  `~immutable_root cx bt` by
    (fs[optionTheory.IS_SOME_EXISTS] >>
     metis_tac[aug_place_supported_root_not_immutable]) >>
  `target_indices_pre ce cx env bt` by suspend "indices" >>
  `!ee. expr_sim_inv ce cx env ee ==> expr_body_pre ce cx env rhs ee` by
    suspend "rhs" >>
  gvs[supported_stmt_expr_exists_def,supported_assignment_exists_def] >> metis_tac[]
QED

Resume intcall_assign_base_entry[target_info]:
  markerLib.RESUME_TAC >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    fs[body_inv_def] >>
  fs[supported_stmt_def,supported_assignment_def] >>
  Cases_on `supported_target_info tops bindings bt` >>
  gvs[AllCaseEqs()] >>
  fs[supported_target_def] >>
  Cases_on `bt`
  >- (gvs[supported_target_info_def,AllCaseEqs()] >>
      metis_tac[intcall_assign_supported_value_place])
  >- (rename1 `TopLevelNameTarget nsid` >>
      `target_mutable env (TopLevelNameTarget nsid)` by
        (qpat_x_assum `IS_SOME (type_stmts _ _ _)` mp_tac >>
         simp[type_stmt_def,AllCaseEqs()] >> strip_tac >>
         Cases_on `nsid` >>
         gvs[atarget_accepts_def,target_mutable_def,well_typed_expr_def,
             optionTheory.IS_SOME_EXISTS,AllCaseEqs()] >>
         Cases_on `FLOOKUP env.bare_globals (q,r)` >>
         Cases_on `FLOOKUP env.toplevel_vtypes (q,r)` >>
         gvs[] >> Cases_on `x` >> gvs[] ) >>
      `get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
      drule_all intcall_mutable_toplevel_not_supported_immutable >> strip_tac >>
      gvs[] >> drule intcall_scalar_target_info >>
      disch_then (qspec_then `bindings` mp_tac) >> simp[])
  >- (Cases_on `b` >> gvs[] >>
      metis_tac[aug_place_legacy_subscript_info,optionTheory.IS_SOME_EXISTS,
                optionTheory.NOT_SOME_NONE]) >>
  Cases_on `b` >> gvs[] >>
  metis_tac[aug_place_legacy_field_info,optionTheory.IS_SOME_EXISTS,
            optionTheory.NOT_SOME_NONE]
QED

Resume intcall_assign_base_entry[indices]:
  markerLib.RESUME_TAC >>
  `get_module_code cx NONE = SOME tops` by fs[body_inv_def] >>
  `cx_tops cx = tops` by metis_tac[cx_tops_module] >>
  irule aug_place_target_indices_pre >>
  gvs[body_inv_def,body_stmt_safe_def,stmt_exprs_ok_flat,
      supported_stmt_expr_exists_def,supported_assignment_exists_def,
      int_calls_stmt_def,int_calls_atarget_def,
      alloc_limits_stmt_def,alloc_limits_assignment_def,
      listTheory.EVERY_APPEND,listTheory.EVERY_CONJ] >>
  metis_tac[alloc_limits_target_indices_not_extcode,
            call_evaluation_safe_append_left]
QED

Resume intcall_assign_base_entry[rhs]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  irule stmt_expr_body_pre >>
  gvs[body_inv_def,body_stmt_safe_def,stmt_exprs_ok_flat,
      supported_stmt_expr_exists_def,supported_assignment_exists_def,
      int_calls_stmt_def,int_calls_atarget_def,
      alloc_limits_stmt_def,alloc_limits_assignment_def,
      listTheory.EVERY_APPEND,listTheory.EVERY_CONJ] >>
  `cx_tops cx = tops` by metis_tac[cx_tops_module] >>
  `~is_extcode rhs` by metis_tac[allocLimitsPropsTheory.alloc_limits_expr_not_extcode] >>
  gvs[expr_has_evm_run_def] >>
  qexists_tac `[]` >> simp[] >>
  metis_tac[call_evaluation_safe_append_right]
QED

Finalise intcall_assign_base_entry
