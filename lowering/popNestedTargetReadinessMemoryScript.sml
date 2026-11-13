(* Successful target runs carry readiness at their actual source endpoint. *)
Theory popNestedTargetReadinessMemory
Ancestors
  targetPlaceSimMem targetPlaceSimCasesBase targetSubscriptSplit targetSubscriptStorage
  vyperPlaceStoragePreservation vyperStoragePlaceProvenance vyperStorageWritePreservation
  accountsRelProps exprSimHypsDefs gasOutcome gasSummary loweringPosts
  vyperState vyperInterpreter vyperValue vyperStorageBackend

Theorem pop_nested_target_marked_storage_ready[local]:
  target_pre cenv cx env bt es /\
  gas_marked_exec T (ctx,func) (eval_base_place cx bt)
    (es,s0) marks (INL pv) mid (OK t) ==>
  !tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
    slots_in_range (get_storage cx (mid with gas_obs := []) tr) (w2n slot) tv /\
    storage_read_live cx tr (get_storage cx (mid with gas_obs := []) tr) slot tv
Proof
  rpt strip_tac >> gvs[] >>
  drule target_subscript_marked_base_source >>
  disch_then (qspec_then `[]` assume_tac) >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
    metis_tac[target_subscript_marked_base_inv] >>
  `storage_layout_safe cx /\ contract_storage_well_formed cx mid`
    by fs[expr_sim_inv_def] >>
  `contract_storage_well_formed cx (mid with gas_obs := [])` by
    (irule vyperStorageLayoutSafetyTheory.contract_storage_well_formed_storage_frame >>
     qexists `mid` >> simp[] >> Cases >>
     simp[vyperStorageBackendTheory.get_storage_def]) >>
  drule_at (Pat `eval_base_place _ _ _ = _`) eval_base_place_storage_ready >>
  disch_then (qspec_then `mid with gas_obs := []` mp_tac) >> simp[] >> strip_tac >>
  simp[] >> Cases_on `type_slot_size tv = 0`
  >- metis_tac[CONJUNCT1 zero_slot_size_slots_in_range] >>
  drule_at (Pat `eval_base_place _ _ _ = _`) eval_base_place_region >>
  simp[storage_result_region_def] >> strip_tac >>
  irule storage_place_region_slots_in_range >> simp[]
QED

Theorem pop_nested_target_outcome_ready_mem:
  target_pre cenv cx env bt es /\
  gas_outcome T (cx_tops cx) (ctx,func) (eval_base_place cx bt) (es,s0)
    (\res ee t. ?pv. res = INL pv /\
      target_post ctx func cenv cx es sa sb s0 ee pv vt op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r) ==>
  gas_outcome T (cx_tops cx) (ctx,func) (eval_base_place cx bt) (es,s0)
    (\res ee t. ?pv. res = INL pv /\
      target_post ctx func cenv cx es sa sb s0 ee pv vt op t /\
      (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
        slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
        storage_read_live cx tr (get_storage cx ee tr) slot tv) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac) >> qexists `marks`
  >- (disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choosel_then [`res`,`mid`,`rr`] strip_assume_tac) >>
      qexistsl [`res`,`mid`,`rr`] >> simp[] >>
      gvs[] >> rpt strip_tac >>
      drule_all pop_nested_target_marked_storage_ready >> simp[]) >>
  disj2_tac >> metis_tac[]
QED
