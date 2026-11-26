(* The array header at the slot actually returned by the linked target. *)
Theory bodyPopReachedSlotMods
Ancestors
  bodyWriteTargetStageMods bodyAssignNameLinkedSetup exprSimPopNestedBase exprSimPopStorage
  appendStorageGhostPtr stateRelProj placeStoreStorage targetSubscriptStorage
  abiDecodeStaticProps vyperFiniteStoragePreservation vyperStorageRegionWrite
  vyperStoragePlaceObserved vyperStoragePlaceRegion vyperStorageFootprint
  vyperStorageBackend vyperLookupStorage vyperTypeValues vyperStorage
  accountsRelProps sourceUnitExecution loweringStateRelDefs compileEnv
  vfmState venomState ptrDiscipline vyperValue vyperAST vyperInterpreter
  exprSimHypsDefs bodyFullShadowBodyInv bodyPtrDefs loweringPosts
  venomExecSemantics context list words

Theorem pop_slot_root_at_horizon[local]:
  valid_horizon cx st0 H ee.storage_trace /\
  storage_well_formed_on cx ee (FST H) /\
  MEM (StorageRoot tr offset root) ee.storage_trace /\
  storage_subregion root path delta (ArrayTV tv (Dynamic n)) /\
  slot = n2w offset + n2w delta ==>
  MEM (tr,n2w offset,root) (FST H) /\
  w2n slot = w2n (n2w offset : bytes32) + delta /\
  storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic n))) /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword (:256) /\
  slots_in_range (get_storage cx ee tr) (w2n slot) (ArrayTV tv (Dynamic n))
Proof
  strip_tac >>
  `storage_observations_ok cx H ee.storage_trace /\ regions_consistent (FST H)` by
    fs[valid_horizon_def] >>
  drule_all_then assume_tac storage_observations_ok_root >>
  drule_all_then strip_assume_tac place_store_root_layout >>
  drule_then assume_tac storage_subregion_bounds >>
  `0 < type_slot_size (ArrayTV tv (Dynamic n))` by simp[type_slot_size_def] >>
  `w2n (n2w offset : bytes32) + delta < dimword (:256)` by decide_tac >>
  `w2n slot = w2n (n2w offset : bytes32) + delta` by
    (qpat_assum `slot = _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     irule w2n_add_n2w_lt >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (simp[storage_place_observed_def] >>
      qexistsl_tac [`n2w offset`, `root`, `path`, `delta`] >> simp[]) >>
  conj_tac >- decide_tac >>
  qpat_assum `w2n slot = _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
  `slots_in_range (get_storage cx ee tr) (w2n (n2w offset : bytes32)) root` by
    fs[storage_well_formed_on_def] >>
  drule_then drule storage_subregion_slots_in_range >> simp[]
QED

Theorem pop_slot_key_clean[local]:
  stmt_state_rel H ctx func cenv cx ee t /\
  dead_lo_ok_mods H D lo cenv cx /\ ghost_inv_at_mods D lo d cenv cx ee G tn t /\
  storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic n))) ==>
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {}
Proof
  strip_tac >>
  `!raw. storage_read_live H tr raw slot (ArrayTV tv (Dynamic n))` by
    (gen_tac >> irule storage_place_observed_read_live >> simp[type_slot_size_def]) >>
  drule stmt_state_rel_state_rel >>
  disch_then (mp_tac o MATCH_MP state_rel_call_ctx_rel) >>
  simp[call_ctx_rel_def] >> strip_tac >>
  irule (INST_TYPE [alpha |-> ``:256``] storage_dead_key_taint_empty) >>
  qexistsl_tac [`H`, `if tr then contract_transient t else contract_storage t`,
                `tr`, `ArrayTV tv (Dynamic n)`] >>
  simp[type_slot_size_def] >> Cases_on `tr` >>
  gvs[ghost_inv_at_mods_def, stor_taint_ok_at_def, dead_lo_ok_mods_def,
      cx_dead_def, contract_storage_def, contract_transient_def, lookup_account_def]
QED

Theorem pop_reached_slot_header_mods:
  eval_target_place cx bt st = (INL (StoragePlace tr slot vt),ee) /\
  expr_sim_inv_mods mods cenv cx env es /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sm s0 ee
      (PlaceR (StoragePlace tr slot vt)) (Type (ArrayT et (Dynamic n))) r G0 tn0 G tn t) ==>
  ?tv offset root path delta.
    vt = ArrayTV tv (Dynamic n) /\ evaluate_type (get_tenv cx) et = SOME tv /\
    elem_size_in_location cenv (slot_loc tr) et = type_slot_size tv /\
    word_scale (slot_loc tr) = 1 /\ n < dimword (:256) /\
    eval_operand (FST r) t = SOME slot /\ FST (SND r) = SOME (slot_loc tr) /\
    op_prov G (FST r) = NONE /\ op_taint tn (FST r) = {} /\
    MEM (StorageRoot tr offset root) ee.storage_trace /\
    storage_subregion root path delta (ArrayTV tv (Dynamic n)) /\
    slot = n2w offset + n2w delta /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      MEM (tr,n2w offset,root) (FST H) /\
      w2n slot = w2n (n2w offset : bytes32) + delta /\
      storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic n))) /\
      w2n slot + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword (:256) /\
      slots_in_range (get_storage cx ee tr) (w2n slot) (ArrayTV tv (Dynamic n)) /\
      storage_read_live H tr (get_storage cx ee tr) slot (ArrayTV tv (Dynamic n)) /\
      storage_range_agree (get_storage cx ee tr)
        (if tr then contract_transient t else contract_storage t) slot (ArrayTV tv (Dynamic n)) /\
      w2n (lookup_storage slot (get_storage cx ee tr)) <= n /\
      key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
      (if tr then tload slot t else sload slot t) = lookup_storage slot (get_storage cx ee tr))
Proof
  strip_tac >>
  drule_then strip_assume_tac eval_target_place_observed_region >>
  rename1 `MEM (StorageRoot tr offset root) ee.storage_trace` >>
  drule_then assume_tac (iffLR storage_trace_domain_def) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon ee.storage_trace` (drule_then assume_tac)) >>
  drule_then strip_assume_tac write_target_storage_view_mods >>
  drule_then strip_assume_tac evaluate_type_ArrayT_cases >>
  rename1 `evaluate_type (get_tenv cx) et = SOME tv` >>
  qpat_x_assum `vt = ArrayTV _ _` SUBST_ALL_TAC >>
  `n < dimword (:256)` by
    (drule target_storage_array_type_bound >> simp[bound_length_def]) >>
  drule_all_then assume_tac assign_name_memory_bytes_mods >>
  `elem_size_in_location cenv (slot_loc tr) et = type_slot_size tv /\
   word_scale (slot_loc tr) = 1` by
    (Cases_on `tr` >> simp[slot_loc_def, elem_size_in_location_def,
       word_scale_def, is_slot_addressed_def, valueEncodingPropsTheory.type_memory_size_slots,
       arithmeticTheory.ADD_DIV_RWT]) >>
  qexistsl_tac [`tv`, `offset`, `root`, `path`, `delta`] >> simp[] >>
  rpt gen_tac >> disch_tac >>
  first_x_assum (drule_then (strip_assume_tac o MATCH_MP write_target_post_view_mods)) >>
  drule_all_then strip_assume_tac pop_slot_root_at_horizon >>
  `storage_read_live H tr (get_storage cx ee tr) slot (ArrayTV tv (Dynamic n))` by
    (irule storage_place_observed_read_live >> simp[type_slot_size_def]) >>
  drule_all_then assume_tac nested_pop_live_array_agree >>
  drule_then assume_tac nested_pop_array_header_load >>
  drule_then assume_tac pop_array_length_bound >>
  `key_taint (if tr then tn.t_trans else tn.t_stor) slot = {}` by
    (irule pop_slot_key_clean >> rpt (first_assum (irule_at Any)) >> simp[]) >>
  qpat_x_assum `slot = _` SUBST_ALL_TAC >> fs[]
QED
