Theory bodyPtrPopTargetSimIndexSource
Ancestors
  bodyPtrPopTargetDefs bodyPtrPopTargetSimCurrentLocal
  exprSimSubscriptArrayOrigin stmtSimAugAssignPlace stmtSimForArrayFrame
  vyperInterpreter vyperState targetPlaceSim targetPlaceSimDefs exprSimHypsDefs
  vyperTypeSystem vyperTyping vyperAST list finite_map loweringPosts
  exprSimProps vyperTypeEnv vyperTypeInvariants vyperPlaceStatePreservation
  stmtSimAugAssign targetPlaceLive exprSimPopNestedBase vyperPureExpr
  vyperStorageBackend targetLocalLive vyperStorageWritePreservation
  vyperStoragePlaceProvenance vyperPlaceStoragePreservation accountsRelProps

Theorem target_base_memory_root_ptr:
  !bt cx s id path st.
    eval_base_place cx bt s = (INL (PlaceR (MemoryPlace id path)),st) ==>
    target_root bt = NameTarget id
Proof
  `(!e:expr. T) /\ (!bt. !cx s id path st.
    eval_base_place cx bt s = (INL (PlaceR (MemoryPlace id path)),st) ==>
    target_root bt = NameTarget id)` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[] >> rpt conj_tac >> rpt gen_tac
  >- simp[Once evaluate_def, bind_def, get_scopes_def, ignore_bind_def,
          type_check_def, assert_def, return_def, raise_def, AllCaseEqs(), target_root_def]
  >- (PairCases_on `p` >> simp[Once evaluate_def] >> metis_tac[lookup_global_not_memory]) >>
  rpt strip_tac >> qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> drule extend_place_memory_origin >> strip_tac >> gvs[] >>
  simp[target_root_def] >> metis_tac[]
QED

Theorem target_current_local_resolution_ptr:
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  type_place_target env bt = SOME bvt /\
  eval_base_place cx bt es = (INL (PlaceR (MemoryPlace id path)),em) /\
  bind (eval_expr cx e) (read_result cx) em = (INL v,ef) /\
  lookup_scopes id ef.scopes = SOME entry ==>
  ISL (evaluate_subscripts entry.type entry.value path)
Proof
  strip_tac >> drule target_base_memory_root_ptr >> strip_tac >>
  `bind (eval_expr cx e) (read_result cx) (em with gas_obs := em.gas_obs) =
     (INL v,ef)` by simp[] >>
  drule_all local_subscript_index_live >> simp[] >>
  strip_tac >> simp[]
QED

Theorem target_readable_local_type_ptr:
  expr_sim_inv cenv cx env es /\ place_readable cx es (PlaceR (MemoryPlace id path)) ==>
  ?ty entry. FLOOKUP env.var_types id = SOME ty /\
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_type (get_tenv cx) ty = SOME entry.type
Proof
  strip_tac >>
  `?entry. lookup_scopes id es.scopes = SOME entry` by
    (qpat_x_assum `place_readable _ _ _` mp_tac >>
     simp[place_readable_def, read_place_def, get_scopes_def, bind_def,
       lift_option_type_def, return_def, raise_def] >>
     Cases_on `lookup_scopes id es.scopes` >> simp[raise_def]) >>
  fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
     vyperTypeInvariantsTheory.env_scopes_consistent_def] >>
  qpat_x_assum `!id entry. lookup_scopes id es.scopes = SOME entry ==> _`
    (qspecl_then [`id`, `entry`] mp_tac) >> simp[] >>
  Cases_on `FLOOKUP env.var_types id` >> simp[] >> metis_tac[]
QED

Theorem target_index_local_source_ptr:
  expr_sim_inv cenv cx env em /\
  place_readable cx em (PlaceR (MemoryPlace id path)) /\
  expr_sim_inv cenv cx env ef /\
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  type_place_target env bt = SOME bvt /\
  eval_base_place cx bt es = (INL (PlaceR (MemoryPlace id path)),em) /\
  bind (eval_expr cx e) (read_result cx) em = (INL v,ef) /\
  place_ptr_rel cenv cx u (PlaceR (MemoryPlace id path)) a loc (Type aty) ==>
  ?entry tv. lookup_scopes id ef.scopes = SOME entry /\
    evaluate_type (get_tenv cx) aty = SOME tv /\
    subscripts_type entry.type path = SOME tv /\
    ?cv. evaluate_subscripts entry.type entry.value path = INL cv /\
         value_has_type tv cv
Proof
  strip_tac >> drule_all target_readable_local_type_ptr >> strip_tac >>
  drule_all stmtSimAugAssignTheory.expr_sim_inv_local >> strip_tac >>
  `cenv.ce_var_type id = SOME ty` by (fs[expr_sim_inv_def] >> metis_tac[]) >>
  `ISL (evaluate_subscripts entry'.type entry'.value path)` by
    (irule target_current_local_resolution_ptr >> metis_tac[]) >>
  fs[place_ptr_rel_def] >> gvs[] >>
  drule mem_path_offset_sound >> strip_tac >>
  `value_has_type entry'.type entry'.value /\ well_formed_type_value entry'.type` by
    (fs[expr_sim_inv_def, state_well_typed_def] >>
     metis_tac[scope_well_typed_lookup_scopes]) >>
  Cases_on `evaluate_subscripts entry'.type entry'.value path` >> gvs[] >>
  metis_tac[evaluate_subscripts_type]
QED

Theorem target_index_pure_storage_source_ptr:
  storage_layout_safe cx /\ contract_storage_well_formed cx ef /\
  eval_base_place cx bt es = (INL (PlaceR (StoragePlace tr slot tv)),em) /\
  bind (eval_expr cx e) (read_result cx) em = (INL v,ef) ==>
  slots_in_range (get_storage cx ef tr) (w2n slot) tv /\
  storage_read_live cx tr (get_storage cx ef tr) slot tv
Proof
  strip_tac >> Cases_on `type_slot_size tv = 0`
  >- (conj_tac
      >- metis_tac[zero_slot_size_slots_in_range] >>
      mp_tac (Q.ISPEC `slot:bytes32` wordsTheory.w2n_lt) >>
      simp[loweringStateRelDefsTheory.storage_read_live_def]) >>
  `0 < type_slot_size tv` by decide_tac >>
  drule eval_base_place_region >> simp[storage_result_region_def] >> strip_tac >>
  conj_tac
  >- (irule storage_place_region_slots_in_range >> metis_tac[]) >>
  irule storage_place_region_read_live >> metis_tac[]
QED
