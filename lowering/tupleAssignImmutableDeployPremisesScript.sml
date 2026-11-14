(* Static target inputs for a mixed mutable/immutable tuple assignment. *)
Theory tupleAssignImmutableDeployPremises
Ancestors
  bodyAugPlaceTarget bodySim bodyExprPreFacts tupleTargetStoreProps
  targetPlaceSim targetPlaceLive supportedStmts supportedTargets
  supportedDecls supportedExprForms supportedProgram supportedStmtTraverse
  supportedExprTraverse supportedTypes exprSimHypsDefs exprSimDefs
  vyperTypeSystem vyperTypeInvariants vyperTypeValues vyperTypeEnv vyperState
  vyperTypeCallGraph vyperTypeCallStackSoundness allocLimits gasContext list finite_map

Theorem tuple_immutable_member_inputs[local]:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
  MEM (BaseTarget bt) gs ==>
  supported_target tops bindings bt /\
  (?ty. well_typed_atarget env (BaseTarget bt) ty) /\
  alloc_limits_target cenv bt /\
  call_evaluation_safe cx (int_calls_target bt) /\
  (!p. supported_target_exists p bt ==>
    supported_stmt_expr_exists p (Assign (TupleTarget gs) e))
Proof
  strip_tac >>
  `!p. supported_assignments_exists p gs =
        EXISTS (supported_assignment_exists p) gs` by
    (rpt (pop_assum kall_tac) >>
     Induct_on `gs` >> simp[supported_assignment_exists_def]) >>
  `alloc_limits_assignments cenv gs =
     EVERY (alloc_limits_assignment cenv) gs` by
    (rpt (pop_assum kall_tac) >>
     Induct_on `gs` >> simp[alloc_limits_assignment_def]) >>
  `!callee. MEM callee (int_calls_target bt) ==>
     MEM callee (int_calls_atargets gs)` by
    (qpat_x_assum `MEM (BaseTarget bt) gs` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Induct_on `gs` >> simp[int_calls_atarget_def] >>
     rpt strip_tac >> gvs[int_calls_atarget_def] >> metis_tac[]) >>
  conj_tac
  >- (gvs[supported_stmt_def, supported_assignment_def, EVERY_MEM] >>
      first_x_assum drule >> simp[]) >>
  conj_tac
  >- (drule tuple_targets_typing >> strip_tac >>
      drule_all LIST_REL_MEM_IMP >> metis_tac[]) >>
  conj_tac
  >- (gvs[stmt_exprs_ok_def, alloc_limits_stmt_def,
          alloc_limits_assignment_def, EVERY_MEM] >>
      qpat_x_assum `!g. MEM g gs ==> alloc_limits_assignment cenv g`
        (qspec_then `BaseTarget bt` mp_tac) >>
      simp[alloc_limits_assignment_def]) >>
  conj_tac
  >- (irule call_evaluation_safe_mono >>
      qexists_tac `int_calls_stmt (Assign (TupleTarget gs) e)` >>
      simp[int_calls_stmt_def, int_calls_atarget_def]) >>
  simp[supported_stmt_expr_exists_def, supported_assignment_exists_def,
       EXISTS_MEM] >> metis_tac[supported_assignment_exists_def]
QED

Theorem tuple_immutable_targets_ready:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (Assign (TupleTarget gs) e) ==> occurs_abi_decode_target target tops) /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
  cx.in_deploy ==>
  EVERY (\g. ?bt ty. g = BaseTarget bt /\
    supported_target tops bindings bt /\ well_typed_atarget env g ty /\
    EVERY (supported_expr tops) (target_indices bt) /\
    target_indices_pre cenv cx env bt /\
    call_evaluation_safe cx (int_calls_target bt) /\
    (immutable_root cx bt ==> ?nsid. bt = TopLevelNameTarget nsid /\
      IS_SOME (supported_immutable_type tops nsid))) gs
Proof
  strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
  `?bt. g = BaseTarget bt /\ supported_target tops bindings bt` by
    (gvs[supported_stmt_def, supported_assignment_def, EVERY_MEM] >>
     first_x_assum drule >> Cases_on `g` >> simp[]) >>
  gvs[] >> drule_all tuple_immutable_member_inputs >> strip_tac >>
  qexists_tac `ty` >> simp[] >>
  conj_tac >- suspend "supported_indices" >>
  conj_tac >- suspend "indices_pre" >>
  suspend "immutable"
QED

Resume tuple_immutable_targets_ready[supported_indices]:
  Cases_on `bt` >> gvs[supported_target_def, target_indices_def]
  >~ [`SubscriptTarget root key`]
  >- (Cases_on `root` >> gvs[target_indices_def]) >>
  rename1 `AttributeTarget root fld` >>
  Cases_on `root` >> gvs[target_indices_def]
QED

Resume tuple_immutable_targets_ready[indices_pre]:
  Cases_on `bt` >> gvs[supported_target_def, target_indices_pre_def]
  >~ [`AttributeTarget t fld`]
  >- (Cases_on `t` >> gvs[target_indices_pre_def]) >>
  rename1 `target_indices_pre cenv cx env root` >>
  Cases_on `root` >> gvs[target_indices_pre_def] >>
  rename1 `SubscriptTarget (TopLevelNameTarget nsid) key` >>
  gvs[Once alloc_limits_expr_def] >> rpt strip_tac >>
  `well_typed_expr env key` by
    gvs[well_typed_atarget_def, well_typed_target_def,
        type_place_target_SubscriptTarget] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `cx_tops cx = tops` by
    (irule cx_tops_module >> gvs[body_inv_def]) >>
  `!p. supported_expr_exists p key ==>
    supported_stmt_expr_exists p (Assign (TupleTarget gs) e)` by
    (rpt strip_tac >>
     qpat_x_assum `!p. supported_target_exists p _ ==> _`
       (qspec_then `p` mp_tac) >> simp[supported_expr_exists_def]) >>
  `~supported_expr_exists
    (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) key` by
    (gvs[stmt_exprs_ok_flat] >> metis_tac[]) >>
  `!target. supported_expr_exists (expr_abi_decode_target_root target) key ==>
    occurs_abi_decode_target target tops` by metis_tac[] >>
  `!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
    is_dynamic (vyper_to_abi_type (type_env tops) target)` by gvs[body_inv_def] >>
  `(int_calls_expr key <> [] ==> ?ts.
     supported_program ts /\ get_module_code cx NONE = SOME ts /\
     EVERY (\c. IS_SOME (supported_function_decl ts c Internal))
       (int_calls_expr key))` by
    (strip_tac >> qexists_tac `tops` >> gvs[body_inv_def]) >>
  irule (Q.INST [`calls` |-> `[]`] (SPEC_ALL stmt_expr_body_pre)) >>
  gvs[int_calls_expr_def] >> metis_tac[]
QED

Resume tuple_immutable_targets_ready[immutable]:
  strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))` by
    gvs[body_inv_def] >>
  Cases_on `bt` >> gvs[supported_target_def]
  >~ [`NameTarget name`]
  >- gvs[immutable_root_def, target_root_def]
  >~ [`TopLevelNameTarget nsid`]
  >- (Cases_on `IS_SOME (supported_immutable_type tops nsid)` >> simp[] >>
      `IS_SOME (supported_target_info tops bindings (TopLevelNameTarget nsid))` by
        (gvs[supported_scalar_target_def] >>
         Cases_on `supported_variable_decl tops nsid` >> gvs[] >>
         rename1 `_ = SOME decl` >> PairCases_on `decl` >>
         Cases_on `decl0` >> Cases_on `decl1` >> Cases_on `decl3` >> gvs[] >>
         `supported_hashmap_decl tops nsid = NONE` by
           metis_tac[aug_place_variable_excludes_hashmap] >>
         `supported_storage_type tops decl2` by
           (simp[supported_storage_type_def] >>
            simp[Once supported_nested_type_def]) >>
         simp[supported_target_info_def, supported_place_root_def]) >>
      Cases_on `supported_target_info tops bindings (TopLevelNameTarget nsid)` >>
      gvs[] >> drule_all aug_place_supported_root_not_immutable >> simp[])
  >~ [`SubscriptTarget t key`]
  >- (Cases_on `t` >> gvs[] >>
      rename1 `supported_subscript_base tops nsid` >>
      `IS_SOME (supported_target_info tops bindings
        (SubscriptTarget (TopLevelNameTarget nsid) key))` by
        (irule aug_place_legacy_subscript_info >> simp[]) >>
      Cases_on `supported_target_info tops bindings
        (SubscriptTarget (TopLevelNameTarget nsid) key)` >> gvs[] >>
      drule_all aug_place_supported_root_not_immutable >> simp[]) >>
  rename1 `AttributeTarget root fld` >> Cases_on `root` >> gvs[] >>
  rename1 `supported_storage_field_write tops nsid fld` >>
  `IS_SOME (supported_target_info tops bindings
    (AttributeTarget (TopLevelNameTarget nsid) fld))` by
    (irule aug_place_legacy_field_info >> simp[]) >>
  Cases_on `supported_target_info tops bindings
    (AttributeTarget (TopLevelNameTarget nsid) fld)` >> gvs[] >>
  drule_all aug_place_supported_root_not_immutable >> simp[]
QED

Finalise tuple_immutable_targets_ready
