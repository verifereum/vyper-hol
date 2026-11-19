Theory bodyFullSubscriptPopSlotRegion
Ancestors
  vyperFiniteStoragePreservation vyperTypeAssignContext
  stmtSimAugAssignPlaceStorage vyperStoragePlaceObserved
  vyperState vyperStatePreservation vyperStorageBackend vyperStorageTrace
  vyperInterpreter vyperTypeCallGraph vyperTypeSystem vyperStorageFootprint
  vyperStoragePlaceRegion vyperStorage vyperLookupStorage vyperValue integer words

(* The address returned by Pop uses the header before the write. *)
Theorem pop_place_storage_result_shape[local]:
  pop_place cx p t = (INL (PlaceR (StoragePlace tr slot leaf)),u) ==>
  ?parent cap len.
    p = StoragePlace tr parent (ArrayTV leaf (Dynamic cap)) /\
    len = w2n (lookup_storage parent (get_storage cx t tr)) /\
    0 < len /\ slot = parent + n2w (1 + (len - 1) * type_slot_size leaf)
Proof
  Cases_on `p`
  >- (rename1 `StoragePlace b parent tv` >>
      Cases_on `tv` >> simp[pop_place_def, raise_def] >>
      rename1 `ArrayTV el bd` >> Cases_on `bd` >>
      simp[pop_place_def, raise_def, get_storage_backend_eq, bind_def,
           check_def, assert_def, ignore_bind_apply, return_def, AllCaseEqs()] >>
      strip_tac >> gvs[]) >>
  simp[Once pop_place_def] >> strip_tac >>
  rpt (FIRST [dxrule_then (strip_assume_tac o REWRITE_RULE[pairTheory.ELIM_UNCURRY]) bind_split,
              dxrule_then strip_assume_tac ignore_bind_split] >>
       gvs[return_def])
QED

Theorem subscript_pop_result_slot_region:
  !cx ty bt env st tr slot leaf u H.
    well_typed_expr env (Pop ty bt) /\
    runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr (Pop ty bt)) /\
    storage_observations_ok cx H u.storage_trace /\
    eval_expr cx (Pop ty bt) st = (INL (PlaceR (StoragePlace tr slot leaf)),u) ==>
    ?offset root path delta.
      MEM (StorageRoot tr offset root) u.storage_trace /\
      storage_subregion root path delta leaf /\
      slot = n2w offset + n2w delta
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr cx (Pop _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,t)` >>
  Cases_on `target_res` >> simp[] >> strip_tac >>
  `?xs. u.storage_trace = t.storage_trace ++ xs` by
    metis_tac[storage_trace_frame_prefix, storage_trace_frame_pop_place] >>
  `storage_observations_ok cx H t.storage_trace` by fs[] >>
  drule pop_place_storage_result_shape >> strip_tac >> gvs[] >>
  drule eval_target_place_observed_region >> strip_tac >>
  drule well_typed_expr_Pop_dynamic_target >> strip_tac >>
  `well_typed_target env bt (ArrayT ty (Dynamic n))` by
    simp[well_typed_target_def] >>
  `call_evaluation_safe cx (int_calls_target bt)` by fs[int_calls_expr_def] >>
  `storage_well_formed_on cx t (FST H)` by
    (drule_all (cj 8 (Q.SPEC `H` eval_storage_well_formed_on_mutual)) >> simp[]) >>
  `storage_place_observed H (StoragePlace tr parent (ArrayTV leaf (Dynamic cap)))` by
    (simp[storage_place_observed_def] >> metis_tac[storage_observations_ok_root]) >>
  `slots_in_range (get_storage cx t tr) (w2n parent) (ArrayTV leaf (Dynamic cap))` by
    (irule aug_place_observed_slots_in_range >> conj_tac
     >- simp[type_slot_size_def] >>
     qexists `H` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `oldlen = w2n (lookup_storage parent (get_storage cx t tr))` >>
  `oldlen <= cap` by
    fs[Once slots_in_range_def, read_slot_def] >>
  `storage_subregion (ArrayTV leaf (Dynamic cap))
     [ValueSubscript (IntV (&(oldlen - 1)))]
     (1 + (oldlen - 1) * type_slot_size leaf) leaf` by
    (simp[storage_subregion_def] >> decide_tac) >>
  drule_all storage_subregion_append >> strip_tac >>
  goal_assum (drule_at Any) >> qexists `offset` >>
  simp[word_add_n2w, WORD_ADD_ASSOC]
QED
