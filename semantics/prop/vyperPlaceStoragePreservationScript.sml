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

Theorem declared_storage_transition_preserves_contract_storage:
  contract_storage_well_formed cx st /\ storage_layout_safe cx /\
  declared_storage_region cx mid name keys = SOME (tr,root,tv) /\
  slots_in_range (get_storage cx st' tr) (w2n root) tv /\
  get_storage cx st' (~tr) = get_storage cx st (~tr) /\
  (!a. a < dimword(:256) /\
       (a < w2n root \/ w2n root + type_slot_size tv <= a) ==>
       read_slot (get_storage cx st' tr) a = read_slot (get_storage cx st tr) a) ==>
  contract_storage_well_formed cx st'
Proof
  strip_tac >>
  `!mid' name' keys' b slot ty storage st''.
     declared_storage_region cx mid' name' keys' = SOME (b,slot,ty) /\
     get_storage_backend cx b st' = (INL storage,st'') ==>
     slots_in_range storage (w2n slot) ty` by
    (rpt gen_tac >> strip_tac >> gvs[get_storage_backend_eq] >>
     Cases_on `(mid,name,keys) = (mid',name',keys')` >- gvs[] >>
     `slots_in_range (get_storage cx st b) (w2n slot) ty` by
       (irule contract_storage_well_formed_region >>
        goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
        simp[get_storage_backend_eq]) >>
     Cases_on `b = tr`
     >- (gvs[] >>
         `ranges_disjoint (w2n root) (type_slot_size tv) (w2n slot) (type_slot_size ty)` by
           (irule storage_layout_safe_region_separation >>
            goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
            metis_tac[]) >>
         `w2n slot + type_slot_size ty <= dimword(:256)` by
           (irule storage_layout_safe_region_nonoverflow >>
            goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
         irule (CONJUNCT1 storage_interval_congruence_mutual) >>
         simp[] >> qexists `get_storage cx st b` >> simp[] >>
         rpt strip_tac >> first_x_assum irule >>
         gvs[vyperStorageFrameTheory.ranges_disjoint_def] >> decide_tac) >>
     `b = ~tr` by (Cases_on `b` >> Cases_on `tr` >> gvs[]) >> gvs[]) >>
  simp[contract_storage_well_formed_def] >> conj_tac
  >- (simp[vyperLookupStorageTheory.well_formed_storage_def,
          vyperLookupStorageTheory.storage_var_in_range_def] >>
      rpt gen_tac >> strip_tac >>
      `declared_storage_region cx mid' n [] = SOME (is_transient,n2w off,tv')` by
        (irule declared_storage_region_ordinary >> simp[]) >>
      Cases_on `off < dimword(:256)`
      >- (first_x_assum (drule_at Any) >>
          simp[get_storage_backend_eq, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
      `off + type_slot_size tv' <= dimword(:256)` by
        (qpat_x_assum `storage_layout_safe cx` mp_tac >>
         simp[storage_layout_safe_def, vyperLookupStorageTheory.well_formed_layout_def] >> metis_tac[]) >>
      `off = dimword(:256) /\ type_slot_size tv' = 0` by decide_tac >>
      irule (CONJUNCT1 zero_slot_size_slots_in_range) >> simp[]) >>
  metis_tac[]
QED

Theorem append_memory_place_storage:
  append_place cx (MemoryPlace id path) v st = (res,st') ==>
  !tr. get_storage cx st' tr = get_storage cx st tr
Proof
  simp[append_place_def, bind_def] >>
  Cases_on `place_type_value cx (MemoryPlace id path) st` >>
  drule place_type_value_state >> strip_tac >> gvs[] >>
  Cases_on `q` >> gvs[] >>
  rename1 `place_type_value cx (MemoryPlace id path) s = (INL tv,s)` >>
  Cases_on `read_place cx (MemoryPlace id path) s` >>
  drule read_place_state >> strip_tac >> gvs[] >>
  Cases_on `q` >> gvs[] >>
  simp[lift_sum_def, get_scopes_def, lift_option_type_def,
       type_check_def, assert_def, set_scopes_def, write_abi_memory_child_def,
       bind_def, ignore_bind_def, return_def, raise_def, pairTheory.UNCURRY] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[bind_def, ignore_bind_def,
       type_check_def, assert_def, set_scopes_def, return_def, raise_def]) >>
  rpt strip_tac >> Cases_on `tr` >>
  gvs[write_abi_memory_child_def, return_def, raise_def, AllCaseEqs(), get_storage_def]
QED

Theorem append_immutable_place_storage:
  append_place cx (ImmutablePlace src id path) v st = (res,st') ==>
  !tr. get_storage cx st' tr = get_storage cx st tr
Proof
  simp[append_place_def, bind_def] >>
  Cases_on `place_type_value cx (ImmutablePlace src id path) st` >>
  drule place_type_value_state >> strip_tac >> gvs[] >>
  Cases_on `q` >> gvs[] >>
  rename1 `place_type_value cx (ImmutablePlace src id path) s = (INL tv,s)` >>
  Cases_on `read_place cx (ImmutablePlace src id path) s` >>
  drule read_place_state >> strip_tac >> gvs[] >>
  Cases_on `q` >> gvs[] >>
  simp[lift_sum_def, get_immutables_def, get_address_immutables_def,
       lift_option_type_def, set_immutable_def, set_address_immutables_def,
       write_abi_immutables_def, bind_def, ignore_bind_def, return_def, raise_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[bind_def, ignore_bind_def,
       set_address_immutables_def, return_def, raise_def]) >>
  rpt strip_tac >> Cases_on `tr` >>
  gvs[write_abi_immutables_def, return_def, raise_def, AllCaseEqs(), get_storage_def]
QED

Theorem pop_memory_place_storage:
  pop_place cx (MemoryPlace id path) st = (res,st') ==>
  !tr. get_storage cx st' tr = get_storage cx st tr
Proof
  simp[pop_place_def, bind_def, get_scopes_def, lift_option_type_def,
       type_check_def, assert_def, lift_sum_def, set_scopes_def,
       return_def, raise_def, ignore_bind_def, check_def, pairTheory.UNCURRY,
       write_abi_memory_child_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[bind_def, ignore_bind_def, type_check_def, assert_def,
           lift_sum_def, set_scopes_def, return_def, raise_def]) >>
  rpt strip_tac >> Cases_on `tr` >>
  gvs[write_abi_memory_child_def, return_def, raise_def, AllCaseEqs(),
      get_storage_scopes, get_storage_def]
QED

Theorem pop_immutable_place_storage:
  pop_place cx (ImmutablePlace src id path) st = (res,st') ==>
  !tr. get_storage cx st' tr = get_storage cx st tr
Proof
  simp[pop_place_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_type_def, lift_sum_def,
       set_immutable_def, set_address_immutables_def, return_def, raise_def,
       ignore_bind_def, write_abi_immutables_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  rpt strip_tac >> Cases_on `tr` >>
  gvs[write_abi_immutables_def, return_def, raise_def, AllCaseEqs(), get_storage_def]
QED

Theorem append_place_preserves_contract_storage:
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  storage_place_region cx p /\
  runtime_place_typed cx st p (ArrayTV etv (Dynamic n)) /\
  value_has_type etv v /\
  append_place cx p v st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  Cases_on `p` >> strip_tac
  >- (gvs[runtime_place_typed_storage] >>
      `0 < type_slot_size (ArrayTV etv (Dynamic n))` by simp[vyperValueTheory.type_slot_size_def] >>
      drule_all storage_place_region_numeric >> strip_tac >>
      `slots_in_range (get_storage cx st b) (w2n root) tv` by
        (irule contract_storage_well_formed_region >>
         goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
         simp[get_storage_backend_eq]) >>
      `slots_in_range (get_storage cx st' b) (w2n root) tv` by
        (drule_all storage_subregion_append_preserves_root >> simp[]) >>
      `w2n c + type_slot_size (ArrayTV etv (Dynamic n)) <= dimword(:256)` by decide_tac >>
      drule_all storage_append_footprint >> strip_tac >>
      irule declared_storage_transition_preserves_contract_storage >>
      simp[] >> qexistsl [`keys`,`mid`,`name`,`root`] >>
      goal_assum (drule_at Any) >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac)
  >- (drule append_memory_place_storage >> strip_tac >>
      irule contract_storage_well_formed_storage_frame >>
      goal_assum (drule_at Any) >> simp[]) >>
  drule append_immutable_place_storage >> strip_tac >>
  irule contract_storage_well_formed_storage_frame >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem pop_place_preserves_contract_storage:
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  storage_place_region cx p /\
  runtime_place_typed cx st p (ArrayTV etv (Dynamic n)) /\
  pop_place cx p st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  Cases_on `p` >> strip_tac
  >- (gvs[runtime_place_typed_storage] >>
      `0 < type_slot_size (ArrayTV etv (Dynamic n))` by simp[vyperValueTheory.type_slot_size_def] >>
      drule_all storage_place_region_numeric >> strip_tac >>
      `slots_in_range (get_storage cx st b) (w2n root) tv` by
        (irule contract_storage_well_formed_region >>
         goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
         simp[get_storage_backend_eq]) >>
      `slots_in_range (get_storage cx st' b) (w2n root) tv` by
        (drule_all storage_subregion_pop_preserves_root >> simp[]) >>
      `w2n c + type_slot_size (ArrayTV etv (Dynamic n)) <= dimword(:256)` by decide_tac >>
      drule_all storage_pop_footprint >> strip_tac >>
      irule declared_storage_transition_preserves_contract_storage >>
      simp[] >> qexistsl [`keys`,`mid`,`name`,`root`] >>
      goal_assum (drule_at Any) >> simp[] >>
      rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac)
  >- (drule pop_memory_place_storage >> strip_tac >>
      irule contract_storage_well_formed_storage_frame >>
      goal_assum (drule_at Any) >> simp[]) >>
  drule pop_immutable_place_storage >> strip_tac >>
  irule contract_storage_well_formed_storage_frame >>
  goal_assum (drule_at Any) >> simp[]
QED

val _ = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn oracle => oracle = "DISK_THM") oracles then ()
    else raise Fail (name ^ " is not closed")
  end)
  [("append_place_preserves_contract_storage",append_place_preserves_contract_storage),
   ("pop_place_preserves_contract_storage",pop_place_preserves_contract_storage)];
