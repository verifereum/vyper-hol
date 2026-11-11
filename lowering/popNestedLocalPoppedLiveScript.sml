Theory popNestedLocalPoppedLive
Ancestors
  popNestedLocalPoppedBridge popNestedLocalPoppedShape
  popNestedLocalPoppedOverlap vyperState vyperInterpreter
  vyperPlaceResultTyping vyperTypeInvariants vyperTypeSystem vyperAST
  exprSimHypsDefs targetPlaceSim targetPlaceSimCasesBase allocLimits
  vyperTypeEvalSoundness vyperTypeExprSoundness
  vyperTypeEvalStoragePreservation vyperTypeCallStackSoundness

Theorem extend_live_memory_path[local]:
  lookup_scopes id s.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value p = INL old /\
  extend_place cx (PlaceR (MemoryPlace id p)) sb s =
    (INL (PlaceR (MemoryPlace id (p ++ [sb]))),t) ==>
  ?live. evaluate_subscripts entry.type entry.value (p ++ [sb]) = INL live
Proof
  rpt strip_tac >>
  qpat_x_assum `extend_place _ _ _ _ = _` mp_tac >>
  simp[extend_place_def, place_type_value_def, read_place_def,
       bind_def, get_scopes_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def, ignore_bind_def, read_memory_path_def,
       AllCaseEqs()] >>
  strip_tac >>
  Cases_on `subscripts_type entry.type p` >>
  gvs[return_def, raise_def, read_memory_path_def] >>
  Cases_on `evaluate_subscripts tv old [sb]` >>
  gvs[return_def, raise_def] >>
  drule_all evaluate_subscripts_append >> metis_tac[]
QED

Theorem local_base_target_live[local]:
  !bt cenv cx env es0 s ty id path t entry.
    (!e st res st'. eval_expr cx e st = (res,st') /\
       ~MEM (WriteAcc (LocalRef id)) (accesses_expr e) ==>
       lookup_scopes id st'.scopes = lookup_scopes id st.scopes) /\
    expr_sim_inv cenv cx env es0 /\ runtime_consistent env cx s /\
    functions_well_typed cx /\
    type_place_target env bt = SOME (Type ty) /\
    target_root bt = NameTarget id /\
    call_evaluation_safe cx (int_calls_target bt) /\
    alloc_limits_target cenv bt /\
    eval_base_place cx bt s = (INL (PlaceR (MemoryPlace id path)),t) /\
    lookup_scopes id t.scopes = SOME entry ==>
    ?live. evaluate_subscripts entry.type entry.value path = INL live
Proof
  Induct using base_assignment_target_induct
  >- (simp[Once evaluate_def, bind_def, get_scopes_def, type_check_def,
           assert_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[evaluate_subscripts_def])
  >- simp[target_root_def]
  >- suspend "subscript"
  >> suspend "attribute"
QED

Resume local_base_target_live[attribute]:
  rpt strip_tac >> gvs[target_root_def] >>
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  drule extend_place_memory_path >> strip_tac >> gvs[] >>
  gvs[vyperTypeCallGraphTheory.int_calls_expr_def, alloc_limits_expr_def] >>
  qpat_x_assum `type_place_target _ (AttributeTarget _ _) = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >>
  drule_all local_target_type_only >> strip_tac >> gvs[] >>
  `?old. evaluate_subscripts entry.type entry.value p = INL old` by
    (first_x_assum drule_all >> simp[]) >>
  irule extend_live_memory_path >> metis_tac[]
QED

Resume local_base_target_live[subscript]:
  rpt strip_tac >> gvs[target_root_def] >>
  drule_all local_subscript_type >> strip_tac >>
  qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >>
  drule extend_place_memory_path >> strip_tac >> gvs[] >>
  drule read_result_state >> strip_tac >> gvs[] >>
  rename1 `eval_base_place cx bt s = (INL (PlaceR (MemoryPlace id p)),sbase)` >>
  rename1 `eval_expr cx e sbase = (INL tv,sidx)` >>
  gvs[alloc_limits_expr_def] >>
  `call_evaluation_safe cx (int_calls_target bt) /\
   call_evaluation_safe cx (int_calls_expr e)` by
    (conj_tac >> irule call_evaluation_safe_mono >>
     goal_assum (drule_at Any) >> simp[vyperTypeCallGraphTheory.int_calls_expr_def]) >>
  `runtime_consistent env cx sbase` by
    metis_tac[eval_base_place_preserves_runtime_consistent] >>
  `runtime_consistent env cx sidx` by
    metis_tac[eval_expr_preserves_runtime_consistent] >>
  drule_all local_target_root_var_type >> strip_tac >>
  `?base_entry. lookup_scopes id sbase.scopes = SOME base_entry` by
    metis_tac[runtime_root_entry] >>
  `?old. evaluate_subscripts base_entry.type base_entry.value p = INL old` by
    (first_x_assum drule_all >> simp[]) >>
  `?old. evaluate_subscripts entry.type entry.value p = INL old` by
    (Cases_on `target_through_dynarray cenv bt`
     >- (drule_all local_target_overlap_excludes_write >>
         simp[vyperSubscriptOverlapTheory.expr_accesses_def] >>
         strip_tac >>
         `lookup_scopes id sidx.scopes = lookup_scopes id sbase.scopes` by
           metis_tac[] >> gvs[] >> metis_tac[]) >>
     `base_entry.type = entry.type` by
       metis_tac[local_root_entry_type] >>
     `fixed_shape_path base_entry.type p` by
       (drule_all local_base_fixed_shape_general >> simp[]) >>
     `value_has_type base_entry.type base_entry.value /\
      well_formed_type_value base_entry.type` by
       (irule vyperTypeEnvTheory.scope_well_typed_lookup_scopes >>
        qexistsl [`id`,`sbase.scopes`] >>
        gvs[runtime_consistent_def, state_well_typed_def]) >>
     `value_has_type entry.type entry.value /\
      well_formed_type_value entry.type` by
       (irule vyperTypeEnvTheory.scope_well_typed_lookup_scopes >>
        qexistsl [`id`,`sidx.scopes`] >>
        gvs[runtime_consistent_def, state_well_typed_def]) >>
     irule fixed_shape_path_transport >> metis_tac[]) >>
  irule extend_live_memory_path >> metis_tac[]
QED

Finalise local_base_target_live

Theorem local_target_live:
  !cenv cx env s bt ty id path t entry.
    (!e st res st'. eval_expr cx e st = (res,st') /\
       ~MEM (WriteAcc (LocalRef id)) (accesses_expr e) ==>
       lookup_scopes id st'.scopes = lookup_scopes id st.scopes) /\
    expr_sim_inv cenv cx env s /\
    type_place_target env bt = SOME (Type ty) /\
    target_root bt = NameTarget id /\
    call_evaluation_safe cx (int_calls_target bt) /\
    alloc_limits_target cenv bt /\
    eval_target_place cx bt s = (INL (MemoryPlace id path),t) /\
    lookup_scopes id t.scopes = SOME entry ==>
    ?live. evaluate_subscripts entry.type entry.value path = INL live
Proof
  rpt strip_tac >>
  `runtime_consistent env cx s /\ functions_well_typed cx` by
    gvs[expr_sim_inv_def, runtime_consistent_def] >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_place_def, AllCaseEqs()] >>
  strip_tac >> Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  irule local_base_target_live >> metis_tac[]
QED
