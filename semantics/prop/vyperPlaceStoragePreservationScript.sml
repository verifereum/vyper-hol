(* TOP-LEVEL: cached-place writes preserve declared storage regions.
   Capacity paths survive intervening changes to dynamic-array lengths. *)
Theory vyperPlaceStoragePreservation
Ancestors
  arithmetic words vyperState vyperTyping vyperStorageBackend
  vyperStorageLayoutSafety vyperStorageWritePreservation
  vyperStoragePlaceRegion vyperStorageRegionWrite vyperStoragePlaceProvenance
  vyperPlaceTyping vyperPlaceFrames vyperTypeStoragePreservation
Libs
  wordsLib

Theorem storage_place_region_numeric:
  storage_layout_safe cx /\
  storage_place_region cx (StoragePlace tr slot leaf) /\
  0 < type_slot_size leaf ==>
  ?mid name keys root tv path delta.
    declared_storage_region cx mid name keys = SOME (tr,root,tv) /\
    storage_subregion tv path delta leaf /\
    w2n slot = w2n root + delta /\
    w2n root + type_slot_size tv <= dimword(:256) /\
    delta + type_slot_size leaf <= type_slot_size tv
Proof
  simp_tac (srw_ss()) [storage_place_region_def] >> strip_tac >>
  drule_all storage_layout_safe_region_nonoverflow >> strip_tac >>
  drule storage_subregion_bounds >> strip_tac >>
  `w2n root + delta < dimword(:256)` by decide_tac >>
  qexistsl_tac [`mid`,`var_name`,`keys`,`root`,`tv`,`path`,`delta`] >>
  simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w,
       arithmeticTheory.MOD_LESS] >> fs[wordsTheory.dimword_def] >> decide_tac
QED

Theorem write_storage_place_preserves_contract_storage:
  contract_storage_well_formed cx st /\ storage_layout_safe cx /\
  storage_place_region cx (StoragePlace tr slot leaf) /\
  well_formed_type_value leaf /\ value_has_type leaf v /\
  write_storage_slot cx tr slot leaf v st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >> Cases_on `type_slot_size leaf = 0`
  >- (drule_all zero_slot_write_storage_frame >> strip_tac >>
      irule contract_storage_well_formed_storage_frame >>
      goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `res`
  >- (Cases_on `x` >>
      `0 < type_slot_size leaf` by decide_tac >>
      drule_all storage_place_region_numeric >> strip_tac >>
      `slots_in_range (get_storage cx st tr) (w2n root) tv` by
        (irule contract_storage_well_formed_region >>
         goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
         simp[get_storage_backend_eq]) >>
      `slots_in_range (get_storage cx st' tr) (w2n root) tv` by
        (drule_all storage_subregion_typed_write_preserves_root >> simp[]) >>
      irule contained_write_preserves_contract_storage_well_formed >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`st`,`slot`,`leaf`,`v`] >> simp[] >> decide_tac) >>
  gvs[write_storage_slot_eq, AllCaseEqs()]
QED

Theorem write_place_preserves_contract_storage:
  contract_storage_well_formed cx st /\ storage_layout_safe cx /\
  storage_place_region cx p /\ runtime_place_typed cx st p tv /\
  value_has_type tv v /\ write_place cx p v st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  Cases_on `p` >> strip_tac
  >- (gvs[write_place_def] >>
      drule_all write_storage_place_preserves_contract_storage >> simp[])
  >- (drule write_memory_place_storage >> strip_tac >>
      irule contract_storage_well_formed_storage_frame >>
      goal_assum (drule_at Any) >> simp[]) >>
  drule write_immutable_place_storage >> strip_tac >>
  irule contract_storage_well_formed_storage_frame >>
  goal_assum (drule_at Any) >> simp[]
QED
