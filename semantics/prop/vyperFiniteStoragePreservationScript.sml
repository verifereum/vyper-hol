(* Storage preservation over a fixed finite horizon of actual observations. *)
Theory vyperFiniteStoragePreservation
Ancestors
  list vyperStorageFootprint vyperStorageTrace vyperTypeEvalStoragePreservation
  vyperTypeEvalSoundness vyperTypeSystem vyperTypeExprSoundness
  vyperTypeStmtSoundness vyperTypeCallStackSoundness vyperEvalMisc
  vyperStorageRegionWrite vyperStoragePlaceRegion vyperTypeStoragePreservation
  vyperStorageBackend vyperStoragePlaceProvenance words
  vyperPlaceTyping vyperPlaceFrames vyperPlaceStoragePreservation
  vyperTypeCallGraph vyperInterpreter vyperState vyperValue
  vyperStaticCallFrame
Libs
  wordsLib

Theorem storage_well_formed_on_stk[local]:
  storage_well_formed_on (cx with stk updated_by f) st R <=>
  storage_well_formed_on cx st R
Proof
  `!b. get_storage (cx with stk updated_by f) st b = get_storage cx st b` by
    (Cases_on `b` >> simp[get_storage_def]) >>
  simp[storage_well_formed_on_def]
QED

Theorem storage_well_formed_on_scopes[local]:
  storage_well_formed_on cx (st with scopes := sc) R <=>
  storage_well_formed_on cx st R
Proof
  irule storage_well_formed_on_backends >> simp[]
QED

Theorem storage_observations_ok_stk[local]:
  storage_observations_ok (cx with stk updated_by f) H tr <=>
  storage_observations_ok cx H tr
Proof
  simp[storage_observations_ok_def, storage_trace_backends_well_formed_def,
       storage_well_formed_on_stk]
QED

Theorem default_finally_preserves_storage_well_formed_on[local]:
  (!r t. eval_exprs cxd ds (st with scopes := [FEMPTY]) = (r,t) /\
         storage_observations_ok cxd H t.storage_trace ==>
         storage_well_formed_on cxd t (FST H)) /\
  storage_observations_ok cxd H out.storage_trace /\
  finally (do set_scopes [FEMPTY]; eval_exprs cxd ds od)
          (set_scopes prev) st = (res,out) ==>
  storage_well_formed_on cxd out (FST H)
Proof
  simp[finally_def, ignore_bind_def, bind_def, set_scopes_def, return_def] >>
  Cases_on `eval_exprs cxd ds (st with scopes := [FEMPTY])` >>
  rename1 `eval_exprs cxd ds (st with scopes := [FEMPTY]) = (dres,dst)` >>
  Cases_on `dres` >>
  simp[ignore_bind_def, bind_def, set_scopes_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[storage_well_formed_on_scopes] >>
  first_x_assum irule >> simp[]
QED

Theorem default_finally_result[local]:
  finally (do set_scopes [FEMPTY]; eval_exprs cxd ds od)
    (set_scopes base_st.scopes) base_st = (res,out) ==>
  ?framed. eval_exprs cxd ds (base_st with scopes := [FEMPTY]) = (res,framed) /\
           out = framed with scopes := base_st.scopes
Proof
  simp[finally_def, ignore_bind_def, bind_def, set_scopes_def, return_def] >>
  Cases_on `eval_exprs cxd ds (base_st with scopes := [FEMPTY])` >>
  rename1 `eval_exprs cxd ds (base_st with scopes := [FEMPTY]) = (dres,dst)` >>
  Cases_on `dres` >> simp[raise_def] >> rpt strip_tac >> gvs[]
QED

Theorem default_restore_runtime_projections[local]:
  state_well_typed base_st /\ state_well_typed framed /\
  accounts_well_typed framed.accounts /\
  env_consistent (defaults_env env_body) cxd framed /\
  eval_exprs cxd ds (base_st with scopes := [FEMPTY]) = (res,framed) /\
  out = framed with scopes := base_st.scopes ==>
  state_well_typed out /\ accounts_well_typed out.accounts /\
  out.scopes = base_st.scopes /\
  vyperImmutableMetadataFrame$immutable_metadata_frame base_st out /\
  env_immutables_consistent env_body cxd out
Proof
  rpt strip_tac >> gvs[]
  >- gvs[vyperTypeInvariantsTheory.state_well_typed_def]
  >- (drule (cj 6 vyperImmutableMetadataFrameTheory.eval_metadata_frame_mutual) >>
      simp[vyperImmutableMetadataFrameTheory.immutable_metadata_frame_def] >>
      metis_tac[]) >>
  gvs[vyperTypeInvariantsTheory.env_consistent_def,
      vyperTypeInvariantsTheory.env_immutables_consistent_def, defaults_env_def] >>
  metis_tac[]
QED

Theorem storage_observations_ok_prefix[local]:
  storage_observations_ok cx H (xs ++ ys) ==>
  storage_observations_ok cx H xs
Proof
  simp[storage_observations_ok_append]
QED

Theorem eval_expr_storage_observations_ok_input[local]:
  eval_expr cx e st = (res,st') /\
  storage_observations_ok cx H st'.storage_trace ==>
  storage_observations_ok cx H st.storage_trace
Proof
  metis_tac[storage_trace_frame_prefix, cj 5 evaluate_storage_trace_frame,
            storage_observations_ok_prefix]
QED

Theorem eval_stmts_storage_observations_ok_input[local]:
  eval_stmts cx ss st = (res,st') /\
  storage_observations_ok cx H st'.storage_trace ==>
  storage_observations_ok cx H st.storage_trace
Proof
  metis_tac[storage_trace_frame_prefix, cj 2 evaluate_storage_trace_frame,
            storage_observations_ok_prefix]
QED

Theorem push_empty_scope_runtime_consistent[local]:
  runtime_consistent env cx st ==>
  runtime_consistent env cx (st with scopes := FEMPTY::st.scopes)
Proof
  simp[vyperTypeExprSoundnessTheory.runtime_consistent_def] >> strip_tac >>
  conj_tac
  >- (drule vyperTypeEnvPreservationTheory.push_scope_env_consistent >>
      Cases_on `st` >> simp[evaluation_state_fn_updates]) >>
  irule vyperTypeStatePreservationTheory.push_scope_preserves_state_well_typed >>
  qexistsl [`st`,`()`] >>
  Cases_on `st` >> simp[push_scope_def, return_def, evaluation_state_fn_updates]
QED

Theorem storage_observations_ok_root[local]:
  storage_observations_ok cx H observations /\
  MEM (StorageRoot b offset tv) observations ==>
  MEM (b,n2w offset,tv) (FST H)
Proof
  simp[storage_observations_ok_def, storage_trace_regions_def,
       EVERY_MEM, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> first_x_assum irule >>
  qexists `[(b,n2w offset,tv)]` >> simp[] >>
  qexists `StorageRoot b offset tv` >> simp[]
QED

Theorem storage_observations_ok_lock[local]:
  storage_observations_ok cx H observations /\
  MEM (StorageLock slot) observations ==>
  MEM slot (SND H)
Proof
  simp[storage_observations_ok_def, storage_trace_locks_def,
       EVERY_MEM, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> first_x_assum irule >>
  qexists `[slot]` >> simp[] >>
  qexists `StorageLock slot` >> simp[]
QED

Theorem storage_observations_ok_backend[local]:
  storage_observations_ok cx H observations /\
  MEM (StorageBackend accounts transient) observations ==>
  storage_well_formed_on cx
    (empty_state with <|accounts := accounts; tStorage := transient|>) (FST H)
Proof
  simp[storage_observations_ok_def,
       storage_trace_backends_well_formed_def, EVERY_MEM] >>
  rpt strip_tac >>
  last_x_assum (qspec_then `StorageBackend accounts transient` mp_tac) >>
  simp[]
QED

Theorem lookup_global_observed_region[local]:
  lookup_global cx mid name st =
    (INL (PlaceR (StoragePlace b slot leaf)),st') ==>
  ?offset tv path delta.
    MEM (StorageRoot b offset tv) st'.storage_trace /\
    storage_subregion tv path delta leaf /\
    slot = n2w offset + n2w delta
Proof
  simp[lookup_global_def, ignore_bind_def, record_storage_event_def,
       bind_def, lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
      var_decl_info_CASE_rator, bind_def, lift_option_type_def,
      record_storage_event_def, ignore_bind_def,
      return_def, raise_def, AllCaseEqs()] >>
  qexistsl [`slot'`,`leaf`,`[]`,`0`] >> simp[storage_subregion_def]
QED

Theorem extend_place_observed_region[local]:
  (!b slot leaf. pv = PlaceR (StoragePlace b slot leaf) ==>
    ?offset tv path delta.
      MEM (StorageRoot b offset tv) st.storage_trace /\
      storage_subregion tv path delta leaf /\
      slot = n2w offset + n2w delta) /\
  extend_place cx pv sb st = (INL (PlaceR (StoragePlace b slot leaf)),st') ==>
  ?offset tv path delta.
    MEM (StorageRoot b offset tv) st'.storage_trace /\
    storage_subregion tv path delta leaf /\
    slot = n2w offset + n2w delta
Proof
  Cases_on `pv` >> simp[extend_place_def, raise_def]
  >- (rename1 `PlaceR p` >> Cases_on `p` >>
      simp[extend_place_def, bind_def, return_def, AllCaseEqs(),
           extend_memory_place_def] >> rpt strip_tac >>
      gvs[bind_def, ignore_bind_def, return_def, AllCaseEqs(),
          extend_memory_place_def] >>
      drule extend_storage_place_subregion >> strip_tac >> gvs[] >>
      `?observations. st'.storage_trace = st.storage_trace ++ observations` by
        metis_tac[storage_trace_frame_prefix, storage_trace_frame_extend_storage] >>
      drule_all storage_subregion_append >> strip_tac >>
      goal_assum (drule_at Any) >> simp[MEM_APPEND] >>
      metis_tac[word_add_n2w, WORD_ADD_ASSOC, WORD_ADD_COMM]) >>
  Cases_on `sb` >> simp[extend_place_def, raise_def] >>
  simp[value_type_CASE_rator, bind_def, ignore_bind_def,
       lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[record_storage_event_def, return_def, AllCaseEqs()] >>
  qexistsl [`w2n (hashmap_slot c (encode_hashmap_key t v'))`,
            `leaf`,`[]`,`0`] >> simp[storage_subregion_def]
QED

Theorem eval_base_place_observed_region[local]:
  !bt cx st b slot leaf st'.
  eval_base_place cx bt st = (INL (PlaceR (StoragePlace b slot leaf)),st') ==>
  ?offset tv path delta.
    MEM (StorageRoot b offset tv) st'.storage_trace /\
    storage_subregion tv path delta leaf /\
    slot = n2w offset + n2w delta
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt`
  >- simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
          type_check_def, assert_def, ignore_bind_def, raise_def, AllCaseEqs()]
  >- (PairCases_on `p` >> pure_once_rewrite_tac[evaluate_def] >>
      metis_tac[lookup_global_observed_region])
  >> rpt gen_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >>
  qmatch_assum_rename_tac `eval_base_place cx child st = (INL child_pv,child_st)` >>
  qpat_x_assum `!y. _` (qspec_then `child` mp_tac) >>
  simp[vyperASTTheory.expr_size_def] >> strip_tac >>
  irule (SRULE [] extend_place_observed_region) >>
  goal_assum (drule_at Any) >> rpt gen_tac >> strip_tac >>
  gvs[] >> first_x_assum drule >> strip_tac >>
  qmatch_assum_rename_tac `storage_subregion root_tv base_path base_delta leaf'` >>
  qexistsl [`offset`,`root_tv`,`base_path`,`base_delta`] >> simp[] >-
  (qmatch_assum_rename_tac `eval_expr cx e child_st = (expr_res,expr_st)` >>
   qmatch_assum_rename_tac `read_result cx tv expr_st = (read_res,read_st)` >>
   `?xs. expr_st.storage_trace = child_st.storage_trace ++ xs` by
     metis_tac[storage_trace_frame_prefix, cj 5 evaluate_storage_trace_frame] >>
   `?ys. read_st.storage_trace = expr_st.storage_trace ++ ys` by
     metis_tac[storage_trace_frame_prefix, storage_trace_frame_read_result] >>
   simp[MEM_APPEND])
QED

Theorem eval_target_place_observed_region[local]:
  eval_target_place cx bt st = (INL (StoragePlace b slot leaf),st') ==>
  ?offset tv path delta.
    MEM (StorageRoot b offset tv) st'.storage_trace /\
    storage_subregion tv path delta leaf /\
    slot = n2w offset + n2w delta
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  metis_tac[SRULE [] eval_base_place_observed_region]
QED

Theorem write_subregion_preserves_storage_well_formed_on[local]:
  regions_consistent regions /\ storage_well_formed_on cx st regions /\
  MEM (b,root,tv) regions /\ storage_subregion tv path relative leaf /\
  w2n slot = w2n root + relative /\
  well_formed_type_value leaf /\ value_has_type leaf v /\
  write_storage_slot cx b slot leaf v st = (res,st') ==>
  storage_well_formed_on cx st' regions
Proof
  strip_tac >> Cases_on `type_slot_size leaf = 0`
  >- (drule_all zero_slot_write_storage_frame >> strip_tac >>
      gvs[storage_well_formed_on_def]) >>
  reverse (Cases_on `res`)
  >- gvs[write_storage_slot_eq, AllCaseEqs()] >>
  Cases_on `x` >>
  `0 < type_slot_size leaf` by decide_tac >>
  `w2n root + type_slot_size tv <= dimword(:256)` by
    metis_tac[regions_consistent_def] >>
  `slots_in_range (get_storage cx st b) (w2n root) tv` by
    metis_tac[storage_well_formed_on_def] >>
  `slots_in_range (get_storage cx st' b) (w2n root) tv` by
    (drule_all storage_subregion_typed_write_preserves_root >> simp[]) >>
  drule storage_subregion_bounds >> strip_tac >>
  irule contained_write_preserves_storage_well_formed_on >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`st`,`slot`,`leaf`,`v`] >> simp[] >> decide_tac
QED

Theorem storage_region_transition_preserves_on[local]:
  regions_consistent regions /\ storage_well_formed_on cx st regions /\
  MEM (b,root,tv) regions /\
  slots_in_range (get_storage cx st' b) (w2n root) tv /\
  get_storage cx st' (~b) = get_storage cx st (~b) /\
  (!a. a < dimword(:256) /\
       (a < w2n root \/ w2n root + type_slot_size tv <= a) ==>
       read_slot (get_storage cx st' b) a = read_slot (get_storage cx st b) a) ==>
  storage_well_formed_on cx st' regions
Proof
  strip_tac >> simp[storage_well_formed_on_def] >> rpt strip_tac >>
  rename1 `MEM (b',slot,tv') regions` >>
  Cases_on `(b,root,tv) = (b',slot,tv')` >- gvs[] >>
  `slots_in_range (get_storage cx st b') (w2n slot) tv'` by
    metis_tac[storage_well_formed_on_def] >>
  Cases_on `b' = b`
  >- (gvs[] >>
      `ranges_disjoint (w2n root) (type_slot_size tv)
                       (w2n slot) (type_slot_size tv')` by
        (fs[regions_consistent_def] >> metis_tac[pairTheory.PAIR_EQ]) >>
      `w2n slot + type_slot_size tv' <= dimword(:256)` by
        metis_tac[regions_consistent_def] >>
      irule (cj 1 storage_interval_congruence_mutual) >> simp[] >>
      qexists `get_storage cx st b` >> simp[] >>
      rpt strip_tac >> first_x_assum irule >>
      gvs[vyperStorageFrameTheory.ranges_disjoint_def] >> decide_tac) >>
  `b' = ~b` by (Cases_on `b` >> Cases_on `b'` >> gvs[]) >> gvs[]
QED

Theorem append_subregion_preserves_storage_well_formed_on[local]:
  regions_consistent regions /\ storage_well_formed_on cx st regions /\
  MEM (b,root,tv) regions /\
  storage_subregion tv path delta (ArrayTV etv (Dynamic n)) /\
  w2n slot = w2n root + delta /\
  well_formed_type_value (ArrayTV etv (Dynamic n)) /\ value_has_type etv v /\
  append_place cx (StoragePlace b slot (ArrayTV etv (Dynamic n))) v st = (res,st') ==>
  storage_well_formed_on cx st' regions
Proof
  strip_tac >>
  `w2n root + type_slot_size tv <= dimword(:256)` by
    metis_tac[regions_consistent_def] >>
  `slots_in_range (get_storage cx st b) (w2n root) tv` by
    metis_tac[storage_well_formed_on_def] >>
  `slots_in_range (get_storage cx st' b) (w2n root) tv` by
    (drule_all storage_subregion_append_preserves_root >> simp[]) >>
  drule storage_subregion_bounds >> strip_tac >>
  `w2n slot + type_slot_size (ArrayTV etv (Dynamic n)) <= dimword(:256)` by
    decide_tac >>
  drule_all storage_append_footprint >> strip_tac >>
  irule storage_region_transition_preserves_on >> simp[] >>
  qexistsl [`b`,`root`,`st`,`tv`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac
QED

Theorem pop_subregion_preserves_storage_well_formed_on[local]:
  regions_consistent regions /\ storage_well_formed_on cx st regions /\
  MEM (b,root,tv) regions /\
  storage_subregion tv path delta (ArrayTV etv (Dynamic n)) /\
  w2n slot = w2n root + delta /\
  well_formed_type_value (ArrayTV etv (Dynamic n)) /\
  pop_place cx (StoragePlace b slot (ArrayTV etv (Dynamic n))) st = (res,st') ==>
  storage_well_formed_on cx st' regions
Proof
  strip_tac >>
  `w2n root + type_slot_size tv <= dimword(:256)` by
    metis_tac[regions_consistent_def] >>
  `slots_in_range (get_storage cx st b) (w2n root) tv` by
    metis_tac[storage_well_formed_on_def] >>
  `slots_in_range (get_storage cx st' b) (w2n root) tv` by
    (drule_all storage_subregion_pop_preserves_root >> simp[]) >>
  drule storage_subregion_bounds >> strip_tac >>
  `w2n slot + type_slot_size (ArrayTV etv (Dynamic n)) <= dimword(:256)` by
    decide_tac >>
  drule_all storage_pop_footprint >> strip_tac >>
  irule storage_region_transition_preserves_on >> simp[] >>
  qexistsl [`b`,`root`,`st`,`tv`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac
QED

Theorem storage_subregion_offset_no_wrap[local]:
  regions_consistent regions /\ MEM (b,n2w offset,tv) regions /\
  storage_subregion tv path delta leaf /\ 0 < type_slot_size leaf /\
  (slot : bytes32) = n2w offset + n2w delta ==>
  w2n slot = w2n (n2w offset : bytes32) + delta
Proof
  strip_tac >> drule storage_subregion_bounds >> strip_tac >>
  `w2n (n2w offset : bytes32) + type_slot_size tv <= dimword(:256)` by
    metis_tac[regions_consistent_def] >>
  `w2n (n2w offset : bytes32) + delta < dimword(:256)` by decide_tac >>
  gvs[] >> simp[word_add_def, w2n_n2w, arithmeticTheory.MOD_LESS]
QED

Theorem write_place_preserves_storage_well_formed_on[local]:
  regions_consistent (FST H) /\ storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H observations /\
  (!b slot leaf. p = StoragePlace b slot leaf ==>
    ?offset tv path delta. MEM (StorageRoot b offset tv) observations /\
      storage_subregion tv path delta leaf /\ slot = n2w offset + n2w delta) /\
  runtime_place_typed cx st p leaf_tv /\ value_has_type leaf_tv v /\
  write_place cx p v st = (res,st') ==>
  storage_well_formed_on cx st' (FST H)
Proof
  Cases_on `p` >> strip_tac
  >- (gvs[runtime_place_typed_storage, write_place_def] >>
      Cases_on `type_slot_size leaf_tv = 0`
      >- (drule_all zero_slot_write_storage_frame >> strip_tac >>
          gvs[storage_well_formed_on_def]) >>
      `0 < type_slot_size leaf_tv` by decide_tac >>
      `MEM (b,n2w offset,tv) (FST H)` by
        metis_tac[storage_observations_ok_root] >>
      `w2n (n2w delta + n2w offset : bytes32) =
       w2n (n2w offset : bytes32) + delta` by
        (irule storage_subregion_offset_no_wrap >> simp[] >> metis_tac[]) >>
      drule_all write_subregion_preserves_storage_well_formed_on >> simp[])
  >- (drule write_memory_place_storage >> strip_tac >>
      gvs[storage_well_formed_on_def]) >>
  drule write_immutable_place_storage >> strip_tac >>
  gvs[storage_well_formed_on_def]
QED

Theorem append_place_preserves_storage_well_formed_on[local]:
  regions_consistent (FST H) /\ storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H observations /\
  (!b slot leaf. p = StoragePlace b slot leaf ==>
    ?offset tv path delta. MEM (StorageRoot b offset tv) observations /\
      storage_subregion tv path delta leaf /\ slot = n2w offset + n2w delta) /\
  runtime_place_typed cx st p (ArrayTV etv (Dynamic n)) /\ value_has_type etv v /\
  append_place cx p v st = (res,st') ==>
  storage_well_formed_on cx st' (FST H)
Proof
  Cases_on `p` >> strip_tac
  >- (gvs[runtime_place_typed_storage] >>
      `0 < type_slot_size (ArrayTV etv (Dynamic n))` by
        simp[vyperValueTheory.type_slot_size_def] >>
      `MEM (b,n2w offset,tv) (FST H)` by
        metis_tac[storage_observations_ok_root] >>
      `w2n (n2w delta + n2w offset : bytes32) =
       w2n (n2w offset : bytes32) + delta` by
        (irule storage_subregion_offset_no_wrap >> simp[] >> metis_tac[]) >>
      drule_all append_subregion_preserves_storage_well_formed_on >> simp[])
  >- (drule append_memory_place_storage >> strip_tac >>
      gvs[storage_well_formed_on_def]) >>
  drule append_immutable_place_storage >> strip_tac >>
  gvs[storage_well_formed_on_def]
QED

Theorem pop_place_preserves_storage_well_formed_on[local]:
  regions_consistent (FST H) /\ storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H observations /\
  (!b slot leaf. p = StoragePlace b slot leaf ==>
    ?offset tv path delta. MEM (StorageRoot b offset tv) observations /\
      storage_subregion tv path delta leaf /\ slot = n2w offset + n2w delta) /\
  runtime_place_typed cx st p (ArrayTV etv (Dynamic n)) /\
  pop_place cx p st = (res,st') ==>
  storage_well_formed_on cx st' (FST H)
Proof
  Cases_on `p` >> strip_tac
  >- (gvs[runtime_place_typed_storage] >>
      `0 < type_slot_size (ArrayTV etv (Dynamic n))` by
        simp[vyperValueTheory.type_slot_size_def] >>
      `MEM (b,n2w offset,tv) (FST H)` by
        metis_tac[storage_observations_ok_root] >>
      `w2n (n2w delta + n2w offset : bytes32) =
       w2n (n2w offset : bytes32) + delta` by
        (irule storage_subregion_offset_no_wrap >> simp[] >> metis_tac[]) >>
      drule_all pop_subregion_preserves_storage_well_formed_on >> simp[])
  >- (drule pop_memory_place_storage >> strip_tac >>
      gvs[storage_well_formed_on_def]) >>
  drule pop_immutable_place_storage >> strip_tac >>
  gvs[storage_well_formed_on_def]
QED

Theorem observed_backend_preserves_storage_well_formed_on[local]:
  storage_observations_ok cx H observations /\
  MEM (StorageBackend accounts transient) observations /\
  st'.accounts = accounts /\ st'.tStorage = transient ==>
  storage_well_formed_on cx st' (FST H)
Proof
  strip_tac >> drule_all storage_observations_ok_backend >>
  match_mp_tac EQ_IMPLIES >>
  irule storage_well_formed_on_backends >> simp[]
QED

Theorem eval_raw_call_preserves_storage_well_formed_on[local]:
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H st'.storage_trace /\
  eval_raw_call cx flags target calldata amount gas st = (res,st') ==>
  storage_well_formed_on cx st' (FST H)
Proof
  simp[eval_raw_call_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, lift_option_def, get_accounts_def,
       get_transient_storage_def, update_accounts_def, update_transient_def,
       append_logs_def, record_storage_backend_def, record_storage_event_def,
       return_def, raise_def, COND_RATOR,
       vfmTypesTheory.option_CASE_rator, vfmTypesTheory.prod_CASE_rator,
       vfmTypesTheory.sum_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[pairTheory.UNCURRY_RATOR, pairTheory.UNCURRY_EQ, combinTheory.C_THM,
      combinTheory.o_THM, AllCaseEqs(), COND_RATOR, bind_def, return_def,
      raise_def] >>
  imp_res_tac (SRULE [evaluation_state_component_equality]
    vyperCallOutcomeTheory.take_call_outcome_frame) >>
  gvs[vyperCallOutcomeTheory.adopt_call_outcome_equation, AllCaseEqs()] >>
  TRY (qpat_x_assum `run_raw_call _ _ _ _ _ _ _ _ = SOME result` mp_tac >>
       PairCases_on `result` >> strip_tac >> gvs[]) >>
  imp_res_tac run_raw_call_failure_frame >>
  Cases_on `flags.rcf_is_static` >> gvs[] >>
  TRY (qpat_assum `run_raw_call _ _ _ _ _ _ _ _ = SOME _` kall_tac >>
       drule_all run_raw_call_static_frame >> strip_tac >> gvs[]) >>
  gvs[storage_observations_ok_def, storage_trace_backends_well_formed_def,
      storage_well_formed_on_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `slots_in_range (get_storage cx _ backend) _ _` >>
  first_x_assum (qspecl_then [`backend`,`slot`,`tv`] mp_tac) >>
  Cases_on `backend` >> gvs[get_storage_def]
QED

Theorem eval_send_preserves_storage_well_formed_on[local]:
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H st'.storage_trace /\
  eval_send cx has_gas vs st = (res,st') ==>
  storage_well_formed_on cx st' (FST H)
Proof
  Cases_on `vs` >- (simp[eval_send_def, raise_def] >> rpt strip_tac >> gvs[]) >>
  Cases_on `t` >- (simp[eval_send_def, raise_def] >> rpt strip_tac >> gvs[]) >>
  simp[eval_send_def, bind_def, ignore_bind_def, type_check_def,
       check_def, assert_def, lift_option_type_def, lift_option_def, get_accounts_def,
       get_transient_storage_def, update_accounts_def, update_transient_def,
       append_logs_def, record_storage_backend_def, record_storage_event_def,
       return_def, raise_def, COND_RATOR,
       vfmTypesTheory.option_CASE_rator, vfmTypesTheory.prod_CASE_rator,
       vfmTypesTheory.sum_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[pairTheory.UNCURRY_RATOR, pairTheory.UNCURRY_EQ, combinTheory.C_THM,
      combinTheory.o_THM, AllCaseEqs(), COND_RATOR, bind_def, return_def,
      raise_def, check_def, assert_def] >>
  imp_res_tac (SRULE [evaluation_state_component_equality]
    vyperCallOutcomeTheory.take_call_outcome_frame) >>
  gvs[vyperCallOutcomeTheory.adopt_call_outcome_equation, AllCaseEqs()] >>
  gvs[storage_observations_ok_def, storage_trace_backends_well_formed_def,
      storage_well_formed_on_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `slots_in_range (get_storage cx _ backend) _ _` >>
  first_x_assum (qspecl_then [`backend`,`slot`,`tv`] mp_tac) >>
  Cases_on `backend` >> gvs[get_storage_def]
QED

Theorem eval_ext_call_effects_preserves_storage_well_formed_on[local]:
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H st'.storage_trace /\
  eval_ext_call_effects cx target calldata value_opt gas st.accounts st = (res,st') ==>
  storage_well_formed_on cx st' (FST H)
Proof
  simp[eval_ext_call_effects_def, bind_def, ignore_bind_def,
       assert_def, lift_option_def, get_transient_storage_def,
       update_accounts_def, update_transient_def, append_logs_def,
       record_storage_backend_def, record_storage_event_def,
       return_def, raise_def, COND_RATOR,
       vfmTypesTheory.option_CASE_rator, vfmTypesTheory.prod_CASE_rator,
       vfmTypesTheory.sum_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[pairTheory.UNCURRY_RATOR, pairTheory.UNCURRY_EQ, combinTheory.C_THM,
      combinTheory.o_THM, AllCaseEqs(), COND_RATOR, bind_def, return_def,
      raise_def] >>
  imp_res_tac (SRULE [evaluation_state_component_equality]
    vyperCallOutcomeTheory.take_call_outcome_frame) >>
  gvs[vyperCallOutcomeTheory.adopt_call_outcome_equation, AllCaseEqs()] >>
  TRY (qpat_x_assum `run_ext_call _ _ _ _ _ _ _ _ = SOME result` mp_tac >>
       PairCases_on `result` >> strip_tac >> gvs[]) >>
  imp_res_tac run_ext_call_static_frame >> gvs[] >>
  gvs[storage_observations_ok_def, storage_trace_backends_well_formed_def,
      storage_well_formed_on_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `slots_in_range (get_storage cx _ backend) _ _` >>
  first_x_assum (qspecl_then [`backend`,`slot`,`tv`] mp_tac) >>
  Cases_on `backend` >> gvs[get_storage_def]
QED

Theorem eval_ext_call_preserves_storage_well_formed_on[local]:
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H st'.storage_trace /\
  eval_ext_call cx static_flag skip_check sig_info opts vs st = (res,st') ==>
  storage_well_formed_on cx st' (FST H)
Proof
  PairCases_on `sig_info` >> Cases_on `vs`
  >- (simp[eval_ext_call_def, raise_def] >> rpt strip_tac >> gvs[]) >>
  simp[eval_ext_call_def, bind_def, ignore_bind_def, type_check_def,
       check_def, assert_def, lift_option_type_def, lift_option_def,
       get_accounts_def, return_def, raise_def, COND_RATOR,
       vfmTypesTheory.option_CASE_rator, vfmTypesTheory.prod_CASE_rator,
       vfmTypesTheory.sum_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[pairTheory.UNCURRY_RATOR, pairTheory.UNCURRY_EQ, combinTheory.C_THM,
      combinTheory.o_THM, AllCaseEqs(), COND_RATOR, bind_def, return_def,
      raise_def, lift_sum_runtime_def, lift_sum_def, check_def, assert_def] >>
  gvs[vfmTypesTheory.sum_CASE_rator, vfmTypesTheory.option_CASE_rator,
      AllCaseEqs(), return_def, raise_def] >>
  metis_tac[eval_ext_call_effects_preserves_storage_well_formed_on]
QED
Theorem create_oracle_result_preserves_storage_well_formed_on[local]:
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H st'.storage_trace /\
  create_oracle_result salt value code rof st = (res,st') ==>
  storage_well_formed_on cx st' (FST H)
Proof
  simp[vyperCreateTheory.create_oracle_result_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  imp_res_tac (SRULE [evaluation_state_component_equality]
    vyperCallOutcomeTheory.take_create_outcome_frame) >>
  gvs[vyperCallOutcomeTheory.adopt_call_outcome_equation, AllCaseEqs()] >>
  Cases_on `rq.cr_static` >> Cases_on `rq.cr_kind = MessageCall` >>
  Cases_on `outcome.co_success` >> gvs[] >>
  gvs[storage_observations_ok_def, storage_trace_backends_well_formed_def,
      storage_well_formed_on_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `slots_in_range (get_storage cx _ backend) _ _` >>
  first_x_assum (qspecl_then [`backend`,`slot`,`tv`] mp_tac) >>
  Cases_on `backend` >> gvs[get_storage_def]
QED

Theorem eval_create_preserves_storage_well_formed_on[local]:
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H st'.storage_trace /\
  eval_create cx kind has_salt rof arg_tys vs blueprint_size st = (res,st') ==>
  storage_well_formed_on cx st' (FST H)
Proof
  simp[vyperCreateTheory.eval_create_def, bind_def, ignore_bind_def,
       lift_option_type_def, lift_option_def, check_def, assert_def,
       get_accounts_def, get_transient_storage_def, get_pending_deletions_def,
       update_accounts_def, update_transient_def, update_pending_deletions_def,
       append_logs_def, record_storage_backend_def, record_storage_event_def,
       vyperCreateTheory.create_soft_failure_def, return_def, raise_def,
       COND_RATOR, vfmTypesTheory.option_CASE_rator,
       vfmTypesTheory.prod_CASE_rator, vfmTypesTheory.sum_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs()]
  >- metis_tac[create_oracle_result_preserves_storage_well_formed_on] >>
  gvs[pairTheory.UNCURRY_RATOR, pairTheory.UNCURRY_EQ, combinTheory.C_THM,
      combinTheory.o_THM, AllCaseEqs(), COND_RATOR, bind_def, return_def,
      raise_def] >>
  gvs[storage_observations_ok_def, storage_trace_backends_well_formed_def,
      storage_well_formed_on_def, vyperCreateTheory.create_rollback_accounts_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `slots_in_range (get_storage cx _ backend) _ _` >>
  first_x_assum (qspecl_then [`backend`,`slot`,`tv`] mp_tac) >>
  Cases_on `backend` >> gvs[get_storage_def] >>
  simp[GSYM vfmStateTheory.lookup_account_def,
       vyperCreateTheory.increment_nonce_storage]
QED


Theorem storage_observations_ok_lock_bound[local]:
  storage_observations_ok cx H observations /\
  MEM (StorageLock lock) observations ==>
  lock + 1 <= dimword(:256)
Proof
  simp[storage_observations_ok_def, storage_roots_fit_def, EVERY_MEM] >>
  rpt strip_tac >>
  last_x_assum (qspec_then `StorageLock lock` mp_tac) >> simp[]
QED

Theorem lock_frame_preserves_storage_well_formed_on[local]:
  regions_consistent regions /\ storage_locks_separated regions locks /\
  storage_well_formed_on cx st regions /\ MEM lock locks /\
  lock + 1 <= dimword(:256) /\ st'.accounts = st.accounts /\
  (!addr slot. slot <> n2w lock ==>
    lookup_storage slot (lookup_transient_storage addr st'.tStorage) =
    lookup_storage slot (lookup_transient_storage addr st.tStorage)) ==>
  storage_well_formed_on cx st' regions
Proof
  strip_tac >> simp[storage_well_formed_on_def] >> rpt strip_tac >>
  `slots_in_range (get_storage cx st b) (w2n slot) tv` by
    metis_tac[storage_well_formed_on_def] >>
  reverse (Cases_on `b`) >- gvs[get_storage_def] >>
  `w2n slot + type_slot_size tv <= dimword(:256)` by
    metis_tac[regions_consistent_def] >>
  `ranges_disjoint (w2n slot) (type_slot_size tv) lock 1` by
    metis_tac[storage_locks_separated_def] >>
  irule (cj 1 storage_interval_congruence_mutual) >> simp[] >>
  qexists `get_storage cx st T` >> simp[] >> rpt strip_tac >>
  `a <> lock` by (gvs[vyperStorageFrameTheory.ranges_disjoint_def] >> decide_tac) >>
  `a < dimword(:256) /\ lock < dimword(:256)` by decide_tac >>
  `n2w a <> (n2w lock:bytes32)` by simp[wordsTheory.n2w_11] >>
  fs[get_storage_def, vyperStorageTheory.read_slot_def,
     vfmExecutionTheory.lookup_transient_storage_def]
QED

Theorem acquire_lock_preserves_storage_well_formed_on[local]:
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H observations /\ MEM (StorageLock lock) observations /\
  acquire_nonreentrant_lock addr lock is_view st = (res,st') ==>
  storage_well_formed_on cx st' (FST H)
Proof
  strip_tac >> drule_all storage_observations_ok_lock >> strip_tac >>
  drule_all storage_observations_ok_lock_bound >> strip_tac >>
  drule acquire_nonreentrant_lock_frame >> strip_tac >>
  irule lock_frame_preserves_storage_well_formed_on >> simp[] >>
  qexistsl [`lock`,`SND H`,`st`] >> fs[]
QED

Theorem release_lock_preserves_storage_well_formed_on[local]:
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H observations /\ MEM (StorageLock lock) observations /\
  release_nonreentrant_lock addr lock st = (res,st') ==>
  storage_well_formed_on cx st' (FST H)
Proof
  strip_tac >> drule_all storage_observations_ok_lock >> strip_tac >>
  drule_all storage_observations_ok_lock_bound >> strip_tac >>
  irule lock_frame_preserves_storage_well_formed_on >> simp[] >>
  qexistsl [`lock`,`SND H`,`st`] >> fs[] >>
  qpat_x_assum `release_nonreentrant_lock _ _ _ = _` mp_tac >>
  simp[release_nonreentrant_lock_eq] >> strip_tac >> gvs[] >>
  simp[vfmExecutionTheory.lookup_transient_storage_def,
       vfmExecutionTheory.update_transient_storage_def,
       vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM] >> rpt strip_tac >>
  Cases_on `addr' = addr` >> simp[combinTheory.APPLY_UPDATE_THM]
QED

Theorem intcall_cleanup_preserves_storage_well_formed_on[local]:
  storage_well_formed_on cx st (FST H) /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_observations_ok cx H st'.storage_trace /\
  (do pop_function prev;
      if nr /\ ~is_view then
        case cx.nonreentrant_slot of
          NONE => return ()
        | SOME slot => release_nonreentrant_lock cx.txn.target slot
      else return ()
   od) st = (res,st') ==>
  storage_well_formed_on cx st' (FST H)
Proof
  strip_tac >> Cases_on `nr /\ ~is_view` >>
  gvs[pop_function_def, ignore_bind_apply, set_scopes_def, return_def]
  >- (Cases_on `cx.nonreentrant_slot` >> gvs[return_def]
      >- (gvs[storage_well_formed_on_def] >> rpt strip_tac >>
           first_x_assum drule >> Cases_on `b` >> simp[get_storage_def]) >>
      `storage_well_formed_on cx (st with scopes := prev) (FST H)` by
        ((gvs[storage_well_formed_on_def] >> rpt strip_tac >>
           first_x_assum drule >> Cases_on `b` >> simp[get_storage_def])) >>
      `MEM (StorageLock x) st'.storage_trace` by
        (qpat_x_assum `release_nonreentrant_lock _ _ _ = _` mp_tac >>
         simp[release_nonreentrant_lock_eq] >> strip_tac >> gvs[]) >>
      drule_all release_lock_preserves_storage_well_formed_on >> simp[]) >>
  (gvs[storage_well_formed_on_def] >> rpt strip_tac >>
           first_x_assum drule >> Cases_on `b` >> simp[get_storage_def])
QED

(* Constructor ledger (all subbranches, including failures, share the owner).
   C1.4 -- ordinary frames and recursive sequencing:
     For_nil, Return_SOME, Return_NONE, Pass, Continue, Break,
     RaiseBare, RaiseUnreachable, RaiseReason, RaiseCustomError,
     AssertBare, AssertUnreachable, AssertReason, AssertCustomError,
     Stmts_nil, Stmts_cons, Exprs_nil, Exprs_cons, Results_nil, Results_cons,
     Expr_FlagMember, Expr_Literal, Expr_Name, Expr_TopLevelName,
     Log, Iterator_Array, Iterator_Range, Expr_Attribute, Expr_TypeBuiltin,
     AnnAssign, Assign_Tuple,
     Expr, If, Expr_IfExp, Expr_StructLit, Expr_Builtin, For, For_cons,
     Expr_Subscript, BasePlaceRoot_NameTarget, BasePlaceRoot_TopLevelNameTarget,
     BasePlaceRoot_AttributeTarget, BasePlaceRoot_SubscriptTarget, TargetPlace,
     TupleStores_nil_nil, TupleStores_cons_nil, TupleStores_nil_cons,
     TupleStore_TupleTarget, TupleStores_cons_cons.
   C1.5 -- typed mutation: Assign_Base, Append, AugAssign, Expr_Pop,
     TupleStore_BaseTarget.
   C1.6 -- ordinary calls, backend adoption and locks:
     Expr_Call_RawRevert, Expr_Call_RawLog, Expr_Call_RawCallTarget,
     Expr_Call_RawCallCalldataTarget, Expr_Call_Send,
     Expr_Call_SelfDestructTarget, Expr_Call_CreateTarget,
     Expr_Call_ExtCall, Expr_Call_IntCall.
   Stmts_cons is discharged below as the C1.1 interface probe. *)

(* The horizon may contain a larger selected execution's roots. Its public
   caller supplies the horizon of that exact execution, including failures. *)
Theorem push_loop_runtime_consistent[local]:
  runtime_consistent env cx st /\
  evaluate_type env.type_defs ty = SOME tyv /\
  value_has_type tyv v /\ id NOTIN FDOM env.var_types /\
  push_scope_with_var id tyv v st = (INL (),stp) ==>
  runtime_consistent (extend_local env id ty F) cx stp
Proof
  rpt strip_tac >>
  `env.type_defs = get_tenv cx` by
    metis_tac[vyperTypeExtCallCoreTheory.runtime_consistent_get_tenv] >>
  `well_formed_type_value tyv` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `env_consistent env cx st` by fs[runtime_consistent_def] >>
  qpat_x_assum `push_scope_with_var _ _ _ _ = _` mp_tac >>
  simp[push_scope_with_var_def, return_def] >> strip_tac >> gvs[] >>
  `env_consistent (extend_local env id ty F) cx
    (st with scopes updated_by
      CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>)))` by
    (irule vyperTypeEnvPreservationTheory.push_scope_with_var_env_consistent >>
     metis_tac[]) >>
  fs[runtime_consistent_def, vyperTypeInvariantsTheory.state_well_typed_def,
     vyperTypeInvariantsTheory.scope_well_typed_def,
     finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem pushed_loop_cleanup[local]:
  push_scope_with_var id tyv v st = (INL (),stp) /\
  finally (try do eval_stmts cx body_stmts; return F od handle_loop_exception)
    pop_scope stp = (loop_res,st_after) ==>
  ?res_body st_body.
    eval_stmts cx body_stmts stp = (res_body,st_body) /\
    st_after = st_body with scopes := TL st_body.scopes /\
    eval_for cx tyv id body_stmts [v] st =
      ((case loop_res of INL broke => INL () | INR e => INR e),st_after)
Proof
  rpt strip_tac >> fs[ignore_bind_def] >>
  `eval_for cx tyv id body_stmts [v] st =
    ((case loop_res of INL broke => INL () | INR e => INR e),st_after)` by
    (simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def] >>
     qpat_assum `push_scope_with_var _ _ _ _ = _` (fn th => rewrite_tac[th]) >>
     simp_tac(srw_ss())[] >>
     qpat_assum `finally _ _ _ = _` (fn th => rewrite_tac[th]) >>
     Cases_on `loop_res` >> simp[Once evaluate_def, return_def]) >>
  `stp.scopes <> []` by
    (qpat_x_assum `push_scope_with_var _ _ _ _ = _` mp_tac >>
     simp[push_scope_with_var_def, return_def] >> strip_tac >> gvs[]) >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[finally_def, bind_def, ignore_bind_def,
    try_def, return_def, pop_scope_def, raise_def, handle_loop_exception_def] >>
  Cases_on `eval_stmts cx body_stmts stp` >>
  `r.scopes <> []` by
    (drule vyperEvalPreservesScopesTheory.eval_stmts_preserves_scopes_len >>
     Cases_on `r.scopes` >> Cases_on `stp.scopes` >> simp[]) >>
  Cases_on `r.scopes` >> gvs[] >>
  Cases_on `q` >> gvs[] >>
  Cases_on `y = ContinueException` >> gvs[return_def] >>
  Cases_on `y = BreakException` >> gvs[return_def, raise_def] >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem transfer_value_preserves_storage_well_formed_on[local]:
  storage_well_formed_on cx st regions /\
  vyperInterpreter$transfer_value fromAddr toAddr amount st = (res,st') ==>
  storage_well_formed_on cx st' regions
Proof
  strip_tac >>
  qpat_x_assum `transfer_value _ _ _ _ = _` mp_tac >>
  Cases_on `amount = 0 \/ fromAddr = toAddr`
  >- (simp[transfer_value_def, return_def] >> strip_tac >> gvs[]) >>
  simp[transfer_value_def, bind_apply, ignore_bind_apply,
    get_accounts_def, check_def, assert_def, update_accounts_def,
    return_def, raise_def] >>
  rpt IF_CASES_TAC >> simp_tac(srw_ss())[return_def, raise_def] >>
  strip_tac >> gvs[storage_well_formed_on_def] >> rpt strip_tac >>
  first_x_assum drule >>
  Cases_on `b` >>
  simp[get_storage_def, vfmStateTheory.update_account_def,
    vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM,
    AllCaseEqs()] >>
  rpt IF_CASES_TAC >> gvs[]
QED

Theorem eval_storage_well_formed_on_mutual:
  !H.
  (!cx s. !env ret_ty env' st res st'.
    type_stmt env ret_ty s = SOME env' /\
    runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt s) /\
    storage_observations_ok cx H st'.storage_trace /\
    eval_stmt cx s st = (res,st') ==>
    storage_well_formed_on cx st' (FST H)) /\
  (!cx ss. !env ret_ty env' st res st'.
    type_stmts env ret_ty ss = SOME env' /\
    runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    storage_observations_ok cx H st'.storage_trace /\
    eval_stmts cx ss st = (res,st') ==>
    storage_well_formed_on cx st' (FST H)) /\
  (!cx it. !env ty st res st'.
    well_typed_iterator env ty it /\
    runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_iterator it) /\
    storage_observations_ok cx H st'.storage_trace /\
    eval_iterator cx it st = (res,st') ==>
    storage_well_formed_on cx st' (FST H)) /\
  (!cx tyv id body vs. !env ret_ty ty env_after st res st'.
    evaluate_type env.type_defs ty = SOME tyv /\
    EVERY (value_has_type tyv) vs /\
    id NOTIN FDOM env.var_types /\
    type_stmts (extend_local env id ty F) ret_ty body = SOME env_after /\
    runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts body) /\
    storage_observations_ok cx H st'.storage_trace /\
    eval_for cx tyv id body vs st = (res,st') ==>
    storage_well_formed_on cx st' (FST H)) /\
  (!cx e. !env st res st'.
    runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    storage_observations_ok cx H st'.storage_trace /\
    eval_expr cx e st = (res,st') ==>
    ((well_typed_expr env e ==> storage_well_formed_on cx st' (FST H)) /\
     (!vt. type_place_expr env e = SOME vt ==>
       storage_well_formed_on cx st' (FST H)))) /\
  (!cx es. !env st res st'.
    well_typed_exprs env es /\
    runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_exprs es) /\
    storage_observations_ok cx H st'.storage_trace /\
    eval_exprs cx es st = (res,st') ==>
    storage_well_formed_on cx st' (FST H)) /\
  (!cx bt. !env vt st res st'.
    type_place_target env bt = SOME vt /\
    runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\
    storage_observations_ok cx H st'.storage_trace /\
    eval_base_place cx bt st = (res,st') ==>
    storage_well_formed_on cx st' (FST H)) /\
  (!cx tgt. !env ty st res st'.
    well_typed_target env tgt ty /\
    runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target tgt) /\
    storage_observations_ok cx H st'.storage_trace /\
    eval_target_place cx tgt st = (res,st') ==>
    storage_well_formed_on cx st' (FST H)) /\
  (!cx tgt v. !env ty st res st'.
    well_typed_atarget env tgt ty /\ value_runtime_typed env ty v /\
    runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atarget tgt) /\
    storage_observations_ok cx H st'.storage_trace /\
    assign_tuple_targets cx tgt v st = (res,st') ==>
    storage_well_formed_on cx st' (FST H)) /\
  (!cx tgts vs. !env tys st res st'.
    LIST_REL (\t ty. well_typed_atarget env t ty) tgts tys /\
    LIST_REL (value_runtime_typed env) tys vs /\
    runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atargets tgts) /\
    storage_observations_ok cx H st'.storage_trace /\
    assign_tuple_target_list cx tgts vs st = (res,st') ==>
    storage_well_formed_on cx st' (FST H)) /\
  (!cx es. !env st res st'.
    well_typed_exprs env es /\ runtime_consistent env cx st /\
    regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on cx st (FST H) /\
    functions_well_typed cx /\ call_evaluation_safe cx (int_calls_exprs es) /\
    storage_observations_ok cx H st'.storage_trace /\ eval_expr_results cx es st = (res,st') ==>
    storage_well_formed_on cx st' (FST H))
Proof
  gen_tac >> ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  (fn (g as (asms,w)) =>
    let
      fun head tm = #Name (dest_thy_const (#1 (strip_comb tm)))
      fun app tm =
        let val (h,args) = strip_comb tm
            val n = head h
        in (List.exists (fn s => s = n)
              ["eval_stmt", "eval_stmts", "eval_iterator", "eval_for",
               "eval_expr", "eval_exprs", "eval_expr_results", "eval_base_place", "eval_target_place"]
            andalso length args = (if n = "eval_for" then 6 else 3)) orelse
           (List.exists (fn s => s = n)
              ["assign_tuple_targets", "assign_tuple_target_list"] andalso length args = 4)
        end handle HOL_ERR _ => false
      val body = #2 (strip_forall w)
      val equations = if is_imp body then strip_conj (fst (dest_imp body)) else asms
      val outer = List.filter (fn a => is_eq a andalso app (lhs a)) equations
      val tm = case outer of [equation] => lhs equation
             | _ => raise Fail "Expected one outer evaluator equation"
      val (h,args) = strip_comb tm
      val n = head h
      val arg = el 2 args
      fun shape t = if listSyntax.is_nil t then "nil" else "cons"
      fun expr_label e =
        let val (_,xs) = strip_comb e
        in if head e = "Call" then "Expr_Call_" ^ head (el 2 xs)
           else "Expr_" ^ head e end
      fun stmt_label s =
        let val (_,xs) = strip_comb s
            val c = head s
        in if c = "Return" then "Return_" ^ head (hd xs)
           else if c = "Raise" then head (hd xs)
           else if c = "Assert" then head (el 2 xs)
           else if c = "Assign" then
             (if head (hd xs) = "BaseTarget" then "Assign_Base" else "Assign_Tuple")
           else c end
      val label =
        if n = "eval_stmt" then stmt_label arg
        else if n = "eval_stmts" then "Stmts_" ^ shape arg
        else if n = "eval_iterator" then "Iterator_" ^ head arg
        else if n = "eval_for" then "For_" ^ shape (el 5 args)
        else if n = "eval_expr" then expr_label arg
        else if n = "eval_exprs" then "Exprs_" ^ shape arg
        else if n = "eval_expr_results" then "Results_" ^ shape arg
        else if n = "eval_base_place" then "BasePlaceRoot_" ^ head arg
        else if n = "eval_target_place" then "TargetPlace"
        else if n = "assign_tuple_targets" then "TupleStore_" ^ head arg
        else if n = "assign_tuple_target_list" then
          "TupleStores_" ^ shape arg ^ "_" ^ shape (el 3 args)
        else raise Fail ("Unknown finite storage evaluator: " ^ n)
    in suspend label g end)
QED

Resume eval_storage_well_formed_on_mutual[Stmts_cons]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmts (s::ss))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_stmt s)` by
    (irule call_evaluation_safe_append_left >>
     qexists `int_calls_stmts ss` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts ss)` by
    (irule call_evaluation_safe_append_right >>
     qexists `int_calls_stmt s` >> simp[]) >>
  qpat_x_assum `type_stmts _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, ignore_bind_apply] >>
  Cases_on `eval_stmt cx s st` >>
  rename1 `eval_stmt cx s st = (r1,st1)` >>
  reverse (Cases_on `r1`) >> simp[bind_def] >> rpt strip_tac >> gvs[]
  >- (first_x_assum drule_all >> simp[]) >>
  `?observations. st'.storage_trace = st1.storage_trace ++ observations` by
    (metis_tac[storage_trace_frame_prefix,
               cj 2 evaluate_storage_trace_frame]) >>
  `storage_observations_ok cx H st1.storage_trace` by
    (qpat_x_assum `storage_observations_ok cx H st'.storage_trace` mp_tac >>
     simp[]) >>
  `storage_well_formed_on cx st1 (FST H)` by
    (first_x_assum drule_all >> simp[]) >>
  `runtime_consistent env'' cx st1` by
    (gvs[runtime_consistent_def] >>
     drule_all eval_stmt_type_preservation_success >> simp[]) >>
  qpat_x_assum `!s0 t. eval_stmt _ _ _ = _ ==> _` drule_all >>
  simp[]
QED

Resume eval_storage_well_formed_on_mutual[For_nil]:
  gvs[Once evaluate_def, return_def]
QED

Resume eval_storage_well_formed_on_mutual[Return_NONE]:
  gvs[Once evaluate_def, raise_def]
QED

Resume eval_storage_well_formed_on_mutual[Pass]:
  gvs[Once evaluate_def, return_def]
QED

Resume eval_storage_well_formed_on_mutual[Continue]:
  gvs[Once evaluate_def, raise_def]
QED

Resume eval_storage_well_formed_on_mutual[Break]:
  gvs[Once evaluate_def, raise_def]
QED

Resume eval_storage_well_formed_on_mutual[RaiseBare]:
  gvs[Once evaluate_def, raise_def]
QED

Resume eval_storage_well_formed_on_mutual[RaiseUnreachable]:
  gvs[Once evaluate_def, raise_def]
QED

Resume eval_storage_well_formed_on_mutual[Stmts_nil]:
  gvs[Once evaluate_def, return_def]
QED

Resume eval_storage_well_formed_on_mutual[Exprs_nil]:
  gvs[Once evaluate_def, return_def]
QED

Resume eval_storage_well_formed_on_mutual[Results_nil]:
  gvs[Once evaluate_def, return_def]
QED

Resume eval_storage_well_formed_on_mutual[Expr_Literal]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, return_def] >> strip_tac >> gvs[]
QED

Resume eval_storage_well_formed_on_mutual[Expr_Name]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, get_scopes_def, type_check_def, assert_def,
       ignore_bind_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Resume eval_storage_well_formed_on_mutual[Expr_FlagMember]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  imp_res_tac vyperStatePreservationTheory.lookup_flag_mem_state >> gvs[]
QED

Resume eval_storage_well_formed_on_mutual[Expr_TopLevelName]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  imp_res_tac vyperStatePreservationTheory.lookup_global_state >>
  qpat_x_assum `st' = _` (fn th => once_rewrite_tac[th]) >>
  gvs[storage_well_formed_on_def, get_storage_def]
QED

Resume eval_storage_well_formed_on_mutual[BasePlaceRoot_NameTarget]:
  rpt gen_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, get_scopes_def, type_check_def, assert_def,
       ignore_bind_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Resume eval_storage_well_formed_on_mutual[BasePlaceRoot_TopLevelNameTarget]:
  rpt gen_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  imp_res_tac vyperStatePreservationTheory.lookup_global_state >>
  qpat_x_assum `st' = _` (fn th => once_rewrite_tac[th]) >>
  gvs[storage_well_formed_on_def, get_storage_def]
QED

Resume eval_storage_well_formed_on_mutual[AssertBare]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Assert e AssertBare))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def, APPEND_NIL] >>
  strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,st1)` >>
  reverse (Cases_on `expr_res`) >>
  gvs[bind_def, return_def, raise_def] >> rpt strip_tac >> gvs[]
  >- (first_x_assum drule_all >> simp[]) >>
  `st' = st1` by
    (drule_at (Pat `switch_BoolV _ _ _ _ _ = _`)
       vyperStatePreservationTheory.switch_BoolV_state >>
     simp[return_def, raise_def]) >>
  gvs[] >> first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[AssertUnreachable]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Assert e AssertUnreachable))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def, APPEND_NIL] >>
  strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,st1)` >>
  reverse (Cases_on `expr_res`) >>
  gvs[bind_def, return_def, raise_def] >> rpt strip_tac >> gvs[]
  >- (first_x_assum drule_all >> simp[]) >>
  `st' = st1` by
    (drule_at (Pat `switch_BoolV _ _ _ _ _ = _`)
       vyperStatePreservationTheory.switch_BoolV_state >>
     simp[return_def, raise_def]) >>
  gvs[] >> first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[Expr]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Expr e))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, type_check_def,
    assert_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,st1)` >>
  Cases_on `er` >> gvs[] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[Return_SOME]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Return (SOME e)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_expr_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,st1)` >>
  reverse (Cases_on `er`) >> gvs[] >> rpt strip_tac >> gvs[]
  >- (first_x_assum drule_all >> simp[]) >>
  Cases_on `read_result cx x st1` >> rename1 `read_result cx x st1 = (rr,st2)` >>
  `st2 = st1` by metis_tac[read_result_state] >>
  Cases_on `rr` >> gvs[] >> first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[Iterator_Array]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_iterator (Array e))` mp_tac >>
  pure_rewrite_tac[int_calls_iterator_def] >> strip_tac >>
  qpat_x_assum `well_typed_iterator _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [well_typed_iterator_def]) >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (er,st1)` >>
  reverse (Cases_on `er`) >> gvs[bind_def, return_def]
  >- (rpt strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]) >>
  Cases_on `read_result cx x st1` >>
  rename1 `read_result cx x st1 = (rr,st2)` >>
  `st2 = st1` by metis_tac[read_result_state] >> gvs[] >>
  Cases_on `rr` >> gvs[bind_def, return_def] >> rpt strip_tac >>
  gvs[AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac vyperStatePreservationTheory.lift_option_type_state >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[RaiseReason]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Raise (RaiseReason e)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_raise_reason_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,st1)` >>
  reverse (Cases_on `er`) >> gvs[bind_def, return_def, raise_def]
  >- (rpt strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]) >>
  Cases_on `read_result cx x st1` >> rename1 `read_result cx x st1 = (rr,st2)` >>
  `st2 = st1` by metis_tac[read_result_state] >> gvs[] >>
  Cases_on `rr` >> gvs[bind_def, return_def, raise_def] >> rpt strip_tac >>
  gvs[AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac vyperStatePreservationTheory.lift_option_type_state >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[Expr_Attribute]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (Attribute ty e id))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ (Attribute _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,st1)` >>
  reverse (Cases_on `er`) >> gvs[bind_def, return_def, raise_def]
  >- (rpt strip_tac >> gvs[] >> first_x_assum drule_all >>
      strip_tac >> gvs[Once well_typed_expr_def, AllCaseEqs()]) >>
  rpt strip_tac >>
  imp_res_tac vyperPlaceFramesTheory.select_result_state >> gvs[] >>
  `?suffix. st'.storage_trace = st1.storage_trace ++ suffix` by
    metis_tac[storage_trace_frame_prefix, storage_trace_frame_select] >>
  `storage_observations_ok cx H st1.storage_trace` by
    metis_tac[storage_observations_ok_prefix] >>
  first_x_assum drule_all >> strip_tac >>
  `storage_well_formed_on cx st1 (FST H)` by
    (gvs[Once well_typed_expr_def, AllCaseEqs()]) >>
  qpat_x_assum `st' = _` SUBST1_TAC >>
  gvs[storage_well_formed_on_def, get_storage_def]
QED

Resume eval_storage_well_formed_on_mutual[RaiseCustomError]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Raise (RaiseCustomError err)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_raise_reason_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def, well_typed_custom_error_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  Cases_on `err` >>
  Cases_on `get_module_code cx (FST p)`
  >- gvs[Once evaluate_def, bind_def, lift_option_def, return_def, raise_def] >>
  rename1 `get_module_code cx (FST p) = SOME tops` >>
  Cases_on `lookup_custom_error_args_in (SND p) tops`
  >- gvs[Once evaluate_def, bind_def, lift_option_def, return_def, raise_def] >>
  rename1 `lookup_custom_error_args_in (SND p) tops = SOME params` >>
  Cases_on `order_custom_error_args params (CustomError p l l0)`
  >- gvs[Once evaluate_def, bind_def, lift_option_def, return_def, raise_def] >>
  rename1 `order_custom_error_args params (CustomError p positional kwargs) = SOME es` >>
  first_x_assum (drule_at (Pat `order_custom_error_args _ _ = _`)) >>
  simp[] >> strip_tac >>
  `PERM (custom_error_exprs (CustomError p positional kwargs)) es` by
    (drule vyperASTTheory.order_custom_error_args_perm >> simp[]) >>
  `well_typed_exprs env es` by
    (drule well_typed_exprs_perm >> disch_then (qspec_then `env` mp_tac) >>
     simp[vyperASTTheory.custom_error_exprs_def]) >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (drule call_evaluation_safe_exprs_perm >>
     disch_then (qspec_then `cx` mp_tac) >> simp[]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, lift_option_def, return_def, raise_def] >>
  Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (er,st1)` >>
  reverse (Cases_on `er`) >> gvs[bind_def, return_def, raise_def]
  >- (rpt strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]) >>
  Cases_on `build_custom_error_data (get_tenv cx) (SND p) (MAP SND params) x` >>
  gvs[return_def, raise_def] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[TargetPlace]:
  rpt gen_tac >> strip_tac >> gvs[well_typed_target_def] >>
  qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac get_place_state >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[Exprs_cons]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_exprs (e::es))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `well_typed_exprs env (e::es)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,st1)` >>
  reverse (Cases_on `er`)
  >- (qpat_x_assum `!s'' tv t s' v t'. _` kall_tac >>
      simp_tac(srw_ss())[] >> rpt strip_tac >> gvs[] >>
      first_x_assum drule_all >> simp[]) >>
  simp_tac(srw_ss())[] >>
  Cases_on `read_result cx x st1` >> rename1 `read_result cx x st1 = (rr,st2)` >>
  `st2 = st1` by metis_tac[read_result_state] >>
  BasicProvers.VAR_EQ_TAC >>
  reverse (Cases_on `rr`) >> simp_tac(srw_ss())[]
  >- (rpt strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]) >>
  qpat_x_assum `!s'' tv t s' v t'. _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >> strip_tac >>
  Cases_on `eval_exprs cx es st1` >> rename1 `eval_exprs cx es st1 = (ers,st3)` >>
  Cases_on `ers` >> gvs[bind_def, return_def] >> rpt strip_tac >> gvs[] >>
  `?suffix. st'.storage_trace = st1.storage_trace ++ suffix` by
    metis_tac[storage_trace_frame_prefix, cj 6 evaluate_storage_trace_frame] >>
  `storage_observations_ok cx H st1.storage_trace` by
    metis_tac[storage_observations_ok_prefix] >>
  `storage_well_formed_on cx st1 (FST H)` by
    (first_x_assum drule_all >> simp[]) >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent] >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[Results_cons]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_exprs (e::es))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `well_typed_exprs env (e::es)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr_results _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,st1)` >>
  reverse (Cases_on `er`)
  >- (qpat_x_assum `!s'' v t. eval_expr cx e s'' = (INL v,t) ==> _` kall_tac >>
      simp_tac(srw_ss())[] >> rpt strip_tac >> gvs[] >>
      first_x_assum drule_all >> simp[]) >>
  simp_tac(srw_ss())[] >>
  qpat_x_assum `!s'' v t. eval_expr cx e s'' = (INL v,t) ==> _` (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  strip_tac >>
  Cases_on `eval_expr_results cx es st1` >>
  rename1 `eval_expr_results cx es st1 = (ers,st3)` >>
  Cases_on `ers` >> gvs[bind_def, return_def] >> rpt strip_tac >> gvs[] >>
  `?suffix. st'.storage_trace = st1.storage_trace ++ suffix` by
    metis_tac[storage_trace_frame_prefix, cj 11 evaluate_storage_trace_frame] >>
  `storage_observations_ok cx H st1.storage_trace` by
    metis_tac[storage_observations_ok_prefix] >>
  `storage_well_formed_on cx st1 (FST H)` by
    (first_x_assum drule_all >> simp[]) >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent] >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[Iterator_Range]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_iterator (Range e e'))` mp_tac >>
  pure_rewrite_tac[int_calls_iterator_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `well_typed_iterator _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [well_typed_iterator_def]) >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,st1)` >>
  reverse (Cases_on `er`)
  >- (qpat_x_assum `!s'' tv t s' v t'. _` kall_tac >>
      simp_tac(srw_ss())[] >> rpt strip_tac >> gvs[] >>
      first_x_assum drule_all >> simp[]) >>
  simp_tac(srw_ss())[] >>
  Cases_on `read_result cx x st1` >> rename1 `read_result cx x st1 = (rr,st2)` >>
  `st2 = st1` by metis_tac[read_result_state] >> BasicProvers.VAR_EQ_TAC >>
  reverse (Cases_on `rr`) >> simp_tac(srw_ss())[]
  >- (rpt strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]) >>
  qpat_x_assum `!s'' tv t s' v t'. _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >> strip_tac >>
  Cases_on `eval_expr cx e' st1` >> rename1 `eval_expr cx e' st1 = (er2,st3)` >>
  strip_tac >>
  `st' = st3` by
    (ntac 2 (qpat_x_assum `!env st res st'. _` kall_tac) >>
     Cases_on `er2` >> gvs[AllCaseEqs()] >>
     imp_res_tac read_result_state >>
     imp_res_tac vyperStatePreservationTheory.lift_sum_state >> gvs[return_def]) >>
  qpat_x_assum `st' = st3` SUBST_ALL_TAC >>
  `?suffix. st3.storage_trace = st1.storage_trace ++ suffix` by
    (ntac 2 (qpat_x_assum `!env st res st'. _` kall_tac) >>
     metis_tac[storage_trace_frame_prefix, cj 5 evaluate_storage_trace_frame]) >>
  `storage_observations_ok cx H st1.storage_trace` by
    metis_tac[storage_observations_ok_prefix] >>
  `storage_well_formed_on cx st1 (FST H)` by
    (first_x_assum drule_all >> simp[]) >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent] >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[Expr_TypeBuiltin]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (TypeBuiltin ty tb typ es))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (TypeBuiltin _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  `well_typed_exprs env es` by
    (qpat_x_assum `well_typed_expr env (TypeBuiltin _ _ _ _)` mp_tac >>
     simp_tac(srw_ss())[Once well_typed_expr_def]) >>
  qpat_x_assum `eval_expr _ (TypeBuiltin _ _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, return_def, raise_def] >>
  Cases_on `type_builtin_args_length_ok tb (LENGTH es)`
  >- (simp_tac(srw_ss())[] >>
      qpat_x_assum `!s'' x t. _` (qspecl_then [`st`, `()`, `st`] mp_tac) >>
      simp[type_check_def, assert_def, return_def] >> strip_tac >>
      Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (er,st1)` >>
      Cases_on `er` >> simp_tac(srw_ss())[] >> rpt strip_tac >>
      gvs[AllCaseEqs()] >>
      imp_res_tac vyperStatePreservationTheory.lift_sum_state >> gvs[] >>
      first_x_assum drule_all >> simp[]) >>
  simp_tac(srw_ss())[] >> strip_tac >> gvs[]
QED

Resume eval_storage_well_formed_on_mutual[Expr_StructLit]:
  rpt gen_tac >> strip_tac >>
  `int_calls_exprs (MAP SND kes) = int_calls_named_exprs kes` by
    (rpt (pop_assum kall_tac) >> Induct_on `kes` >> simp[int_calls_expr_def] >>
     Cases >> simp[int_calls_expr_def]) >>
  `call_evaluation_safe cx (int_calls_exprs (MAP SND kes))` by
    (gvs[Once int_calls_expr_def]) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (StructLit _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr _ (StructLit _ _ _)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  `well_typed_exprs env (MAP SND kes)` by
    (irule well_typed_named_exprs_MAP_SND_storage >> simp[]) >>
  qpat_x_assum `eval_expr _ (StructLit _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  qpat_x_assum `!ks. ks = MAP FST kes ==> _` (qspec_then `MAP FST kes` mp_tac) >>
  simp_tac bool_ss [] >> strip_tac >>
  Cases_on `eval_exprs cx (MAP SND kes) st` >>
  rename1 `eval_exprs cx (MAP SND kes) st = (er,st1)` >>
  Cases_on `er` >> simp_tac(srw_ss())[] >> rpt strip_tac >>
  gvs[bind_def, return_def] >> first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[AssertReason]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Assert e (AssertReason e')))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,st1)` >>
  reverse (Cases_on `er`)
  >- (qpat_x_assum `!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> _` kall_tac >>
      simp_tac(srw_ss())[] >> rpt strip_tac >> gvs[] >>
      first_x_assum drule_all >> simp[]) >>
  simp_tac(srw_ss())[switch_BoolV_def, bind_def, return_def, raise_def] >>
  qpat_x_assum `!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >> strip_tac >>
  Cases_on `read_result cx x st1` >> rename1 `read_result cx x st1 = (rr,st2)` >>
  `st2 = st1` by metis_tac[read_result_state] >> BasicProvers.VAR_EQ_TAC >>
  reverse (Cases_on `rr`) >> simp_tac(srw_ss())[]
  >- (rpt strip_tac >> BasicProvers.VAR_EQ_TAC >> first_x_assum drule_all >> simp[]) >>
  Cases_on `x' = BoolV T` >>
  pop_assum (fn th => rewrite_tac[th, return_def, raise_def]) >>
  simp_tac(srw_ss())[]
  >- (rpt strip_tac >> BasicProvers.VAR_EQ_TAC >> first_x_assum drule_all >> simp[]) >>
  reverse (Cases_on `x' = BoolV F`) >>
  pop_assum (fn th => rewrite_tac[th, return_def, raise_def]) >>
  simp_tac(srw_ss())[]
  >- (rpt strip_tac >> BasicProvers.VAR_EQ_TAC >> first_x_assum drule_all >> simp[]) >>
  Cases_on `eval_expr cx e' st1` >> rename1 `eval_expr cx e' st1 = (er2,st3)` >>
  simp_tac(srw_ss())[bind_def, return_def, raise_def] >> strip_tac >>
  `st' = st3` by
    (ntac 2 (qpat_x_assum `!env st res st'. _` kall_tac) >>
     Cases_on `er2` >> gvs[AllCaseEqs()] >> imp_res_tac read_result_state >>
     imp_res_tac vyperStatePreservationTheory.lift_option_type_state >>
     gvs[raise_def]) >>
  qpat_x_assum `st' = st3` SUBST_ALL_TAC >>
  `?suffix. st3.storage_trace = st1.storage_trace ++ suffix` by
    (ntac 2 (qpat_x_assum `!env st res st'. _` kall_tac) >>
     metis_tac[storage_trace_frame_prefix, cj 5 evaluate_storage_trace_frame]) >>
  `storage_observations_ok cx H st1.storage_trace` by
    metis_tac[storage_observations_ok_prefix] >>
  `storage_well_formed_on cx st1 (FST H)` by
    (first_x_assum drule_all >> simp[]) >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent] >>
  first_x_assum drule_all >> simp[]
QED

(* The selected branch equation is exposed by each constructor case. *)
val finite_ifexp_branch_finish =
  `storage_observations_ok cx H st1.storage_trace` by
    (drule_all eval_expr_storage_observations_ok_input >> simp_tac(srw_ss())[]) >>
  `storage_well_formed_on cx st1 (FST H)` by
    (first_x_assum drule_all >> disch_then (mp_tac o CONJUNCT1) >>
     disch_then drule >> simp_tac(srw_ss())[]) >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent] >>
  first_x_assum drule_all >> disch_then (mp_tac o CONJUNCT1) >>
  disch_then drule >> simp_tac(srw_ss())[];

Resume eval_storage_well_formed_on_mutual[Expr_IfExp]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (IfExp ty e e' e''))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_expr e' ++ int_calls_expr e''` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e')` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_expr e' ++ int_calls_expr e''` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e'')` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_expr e' ++ int_calls_expr e''` >> simp[]) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (IfExp _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  disch_then mp_tac >> simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,st1)` >>
  reverse (Cases_on `er`)
  >- (ntac 2 (qpat_x_assum `!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> _` kall_tac) >>
      simp_tac(srw_ss())[] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
      first_x_assum drule_all >> simp[]) >>
  ntac 2 (qpat_x_assum `!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >> strip_tac) >>
  simp_tac(srw_ss())[switch_BoolV_def, bind_def] >>
  Cases_on `read_result cx x st1` >> rename1 `read_result cx x st1 = (rr,st2)` >>
  `st2 = st1` by metis_tac[read_result_state] >> BasicProvers.VAR_EQ_TAC >>
  reverse (Cases_on `rr`)
  >- (simp_tac(srw_ss())[raise_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
      first_x_assum drule_all >> disch_then (mp_tac o CONJUNCT1) >>
      disch_then drule >> simp_tac(srw_ss())[]) >>
  simp_tac(srw_ss())[] >>
  Cases_on `x' = BoolV T` >>
  pop_assum (fn th => rewrite_tac[th])
  >- (qpat_x_assum `!env st res st'. _ ==> (well_typed_expr env e'' ==> _) /\ _` kall_tac >>
      Cases_on `eval_expr cx e' st1` >> rename1 `eval_expr cx e' st1 = (er2,st3)` >>
      strip_tac >>
      `st' = st3` by
        (ntac 2 (qpat_x_assum `!env st res st'. _` kall_tac) >>
         Cases_on `er2` >> gvs[] >> imp_res_tac vyperStatePreservationTheory.conditional_result_state >> gvs[]) >>
      qpat_x_assum `st' = st3` SUBST_ALL_TAC >>
      finite_ifexp_branch_finish) >>
  Cases_on `x' = BoolV F` >>
  pop_assum (fn th => rewrite_tac[th])
  >- (qpat_x_assum `!env st res st'. _ ==> (well_typed_expr env e' ==> _) /\ _` kall_tac >>
      Cases_on `eval_expr cx e'' st1` >> rename1 `eval_expr cx e'' st1 = (er2,st3)` >>
      strip_tac >>
      `st' = st3` by
        (ntac 2 (qpat_x_assum `!env st res st'. _` kall_tac) >>
         Cases_on `er2` >> gvs[] >>
         imp_res_tac vyperStatePreservationTheory.conditional_result_state >> gvs[]) >>
      qpat_x_assum `st' = st3` SUBST_ALL_TAC >>
      finite_ifexp_branch_finish) >>
  simp_tac(srw_ss())[raise_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  first_x_assum drule_all >> disch_then (mp_tac o CONJUNCT1) >>
  disch_then drule >> simp_tac(srw_ss())[]
QED

(* Scope cleanup has already exposed its backend and trace equalities. *)
val finite_if_branch_finish =
  `storage_observations_ok cx H stb.storage_trace` by metis_tac[] >>
  `storage_observations_ok cx H st1.storage_trace` by
    (drule_all eval_stmts_storage_observations_ok_input >> simp_tac(srw_ss())[]) >>
  `storage_well_formed_on cx st1 (FST H)` by
    (first_x_assum drule_all >> disch_then (mp_tac o CONJUNCT1) >>
     disch_then drule >> simp_tac(srw_ss())[]) >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent] >>
  `storage_well_formed_on cx (st1 with scopes := FEMPTY::st1.scopes) (FST H)` by
    (qpat_x_assum `!env ret_ty env' st res st'. _` kall_tac >>
     qpat_x_assum `!env st res st'. _` kall_tac >>
     irule (iffRL storage_well_formed_on_backends) >> qexists `st1` >> simp[]) >>
  `runtime_consistent env cx (st1 with scopes := FEMPTY::st1.scopes)` by
    (irule push_empty_scope_runtime_consistent >> first_assum ACCEPT_TAC) >>
  `storage_well_formed_on cx stb (FST H)` by (first_x_assum drule_all >> simp[]) >>
  metis_tac[storage_well_formed_on_backends];

Resume eval_storage_well_formed_on_mutual[If]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (If e ss ss'))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_stmts ss ++ int_calls_stmts ss'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts ss)` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_stmts ss ++ int_calls_stmts ss'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts ss')` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_stmts ss ++ int_calls_stmts ss'` >> simp[]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,st1)` >>
  reverse (Cases_on `er`)
  >- (ntac 2 (qpat_x_assum `!s'' tv t sp u tp. eval_expr cx e s'' = (INL tv,t) /\ _ ==> _` kall_tac) >>
      simp_tac(srw_ss())[] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
      first_x_assum drule_all >> simp[]) >>
  `push_scope st1 = (INL (),st1 with scopes := FEMPTY::st1.scopes)` by
    (ntac 2 (qpat_x_assum `!s'' tv t sp u tp. _` kall_tac) >>
     qpat_x_assum `!env st res st'. _` kall_tac >>
     Cases_on `st1` >> simp[push_scope_def, return_def, evaluation_state_fn_updates]) >>
  ntac 2 (qpat_x_assum `!s'' tv t sp u tp. eval_expr cx e s'' = (INL tv,t) /\ _ ==> _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >>
    disch_then (drule_at (Pat `push_scope _ = _`)) >> strip_tac) >>
  simp_tac(srw_ss())[ignore_bind_apply] >>
  qpat_assum `push_scope st1 = _` (fn th => rewrite_tac[th]) >>
  simp_tac(srw_ss())[finally_def, switch_BoolV_def, bind_def,
    vyperStatePreservationTheory.read_result_empty_scope] >>
  Cases_on `read_result cx x st1` >> rename1 `read_result cx x st1 = (rr,st2)` >>
  `st2 = st1` by metis_tac[read_result_state] >> BasicProvers.VAR_EQ_TAC >>
  reverse (Cases_on `rr`)
  >- (ntac 2 (qpat_x_assum `!env ret_ty env' st res st'. _` kall_tac) >>
      simp_tac(srw_ss())[ignore_bind_apply, pop_scope_def, return_def, raise_def] >>
      strip_tac >> BasicProvers.VAR_EQ_TAC >>
      first_x_assum drule_all >> simp[]) >>
  simp_tac(srw_ss())[] >>
  Cases_on `x' = BoolV T` >> pop_assum (fn th => rewrite_tac[th])
  >- (qpat_x_assum `!env ret_ty env' st res st'. type_stmts env ret_ty ss' = _ /\ _ ==> _` kall_tac >>
      qpat_x_assum `IS_SOME (type_stmts env ret_ty ss)` mp_tac >>
      simp_tac(srw_ss())[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
      Cases_on `eval_stmts cx ss (st1 with scopes := FEMPTY::st1.scopes)` >>
      rename1 `eval_stmts cx ss (st1 with scopes := FEMPTY::st1.scopes) = (br,stb)` >>
      strip_tac >>
      `st'.storage_trace = stb.storage_trace /\
       st'.accounts = stb.accounts /\ st'.tStorage = stb.tStorage` by
        (qpat_x_assum `!env ret_ty env' st res st'. _` kall_tac >>
         qpat_x_assum `!env st res st'. _` kall_tac >>
         Cases_on `br` >> gvs[ignore_bind_apply, pop_scope_def, return_def, raise_def,
                                 AllCaseEqs()]) >>
      finite_if_branch_finish) >>
  Cases_on `x' = BoolV F` >> pop_assum (fn th => rewrite_tac[th])
  >- (qpat_x_assum `!env ret_ty env' st res st'. type_stmts env ret_ty ss = _ /\ _ ==> _` kall_tac >>
      qpat_x_assum `IS_SOME (type_stmts env ret_ty ss')` mp_tac >>
      simp_tac(srw_ss())[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
      Cases_on `eval_stmts cx ss' (st1 with scopes := FEMPTY::st1.scopes)` >>
      rename1 `eval_stmts cx ss' (st1 with scopes := FEMPTY::st1.scopes) = (br,stb)` >>
      strip_tac >>
      `st'.storage_trace = stb.storage_trace /\
       st'.accounts = stb.accounts /\ st'.tStorage = stb.tStorage` by
        (qpat_x_assum `!env ret_ty env' st res st'. _` kall_tac >>
         qpat_x_assum `!env st res st'. _` kall_tac >>
         Cases_on `br` >> gvs[ignore_bind_apply, pop_scope_def, return_def, raise_def,
                                 AllCaseEqs()]) >>
      finite_if_branch_finish) >>
  ntac 2 (qpat_x_assum `!env ret_ty env' st res st'. _` kall_tac) >>
  simp_tac(srw_ss())[ignore_bind_apply, pop_scope_def, return_def, raise_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >> first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[TupleStores_nil_nil]:
  gvs[Once evaluate_def, return_def]
QED
Resume eval_storage_well_formed_on_mutual[TupleStores_cons_nil]:
  gvs[Once evaluate_def, raise_def]
QED
Resume eval_storage_well_formed_on_mutual[TupleStores_nil_cons]:
  gvs[Once evaluate_def, raise_def]
QED

Resume eval_storage_well_formed_on_mutual[TupleStore_TupleTarget]:
  rpt gen_tac >> strip_tac >>
  gvs[well_typed_atarget_def, int_calls_atarget_def] >>
  drule value_runtime_typed_tuple_components >> strip_tac >> gvs[] >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[TupleStore_BaseTarget]:
  rpt gen_tac >> strip_tac >>
  rename1 `assign_tuple_targets cx (BaseTarget bt) v st = (res,st')` >>
  qpat_x_assum `well_typed_atarget _ _ _` mp_tac >>
  simp_tac(srw_ss())[well_typed_atarget_def] >> strip_tac >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_atarget _)` mp_tac >>
  pure_rewrite_tac[int_calls_atarget_def] >> strip_tac >>
  qpat_x_assum `assign_tuple_targets _ _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (answer,middle)` >>
  reverse (Cases_on `answer`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
      first_x_assum drule_all >> simp[]) >>
  simp_tac(srw_ss())[] >> strip_tac >>
  `?xs. st'.storage_trace = middle.storage_trace ++ xs` by
    metis_tac[storage_trace_frame_prefix, storage_trace_frame_write_place] >>
  `storage_observations_ok cx H middle.storage_trace` by
    metis_tac[storage_observations_ok_prefix] >>
  `storage_well_formed_on cx middle (FST H)` by
    (first_x_assum drule_all >> simp[]) >>
  drule_all eval_target_place_success_storage_type >>
  simp[vyperTypeInvariantsTheory.eval_result_typed_def] >> strip_tac >>
  gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  irule write_place_preserves_storage_well_formed_on >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  qexistsl [`tv`,`middle.storage_trace`] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`res`,`v`] >> simp[] >>
  rpt strip_tac >> gvs[] >>
  drule eval_target_place_observed_region >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[TupleStores_cons_cons]:
  rpt gen_tac >> strip_tac >>
  rename1 `assign_tuple_target_list cx (g::gs) (v::vs) st = (res,st')` >>
  Cases_on `tys` >- gvs[] >>
  rename1 `LIST_REL _ (g::gs) (head_ty::tail_tys)` >>
  fs[LIST_REL_CONS1] >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_atargets (g::gs))` mp_tac >>
  pure_rewrite_tac[int_calls_atarget_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `assign_tuple_target_list _ _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def] >>
  Cases_on `assign_tuple_targets cx g v st` >>
  rename1 `assign_tuple_targets cx g v st = (answer,middle)` >>
  reverse (Cases_on `answer`)
  >- (simp[] >> strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]) >>
  Cases_on `x` >> simp_tac(srw_ss())[] >> strip_tac >>
  `?xs. st'.storage_trace = middle.storage_trace ++ xs` by
    metis_tac[storage_trace_frame_prefix, cj 10 evaluate_storage_trace_frame] >>
  `storage_observations_ok cx H middle.storage_trace` by
    metis_tac[storage_observations_ok_prefix] >>
  `storage_well_formed_on cx middle (FST H)` by
    (qpat_x_assum `!env ty st res st'. _` drule_all >> simp[]) >>
  `runtime_consistent env cx middle` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_all (cj 9 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual) >>
     simp[]) >>
  qpat_x_assum `!s'' t. assign_tuple_targets _ _ _ s'' = (INL (),t) ==> _`
    (drule_then strip_assume_tac) >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[Append]:
  rpt gen_tac >> strip_tac >>
  rename1 `eval_stmt cx (Append bt e) st = (res,st')` >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Append bt e))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >>
  Cases_on `type_place_target env bt` >- simp[NoAsms] >>
  simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME vt` >>
  Cases_on `vt` >> simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME (Type ty)` >>
  Cases_on `ty` >> simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME (Type (ArrayT elem_ty bd))` >>
  Cases_on `bd` >- simp[NoAsms] >> simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME (Type (ArrayT elem_ty (Dynamic n)))` >>
  strip_tac >> qpat_x_assum `env = env'` (SUBST_ALL_TAC o SYM) >>
  `well_typed_target env bt (ArrayT elem_ty (Dynamic n))` by
    simp[well_typed_target_def] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,st1)` >>
  reverse (Cases_on `target_res`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> gvs[] >>
      qpat_x_assum `!s p t. eval_target_place _ _ _ = _ ==> _` kall_tac >>
      first_x_assum drule_all >> simp[]) >>
  rename1 `eval_target_place cx bt st = (INL p,st1)` >>
  qpat_x_assum `!s p t. eval_target_place _ _ _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  simp_tac(srw_ss())[] >>
  Cases_on `eval_expr cx e st1` >>
  rename1 `eval_expr cx e st1 = (expr_res,st2)` >>
  reverse (Cases_on `expr_res`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> gvs[] >>
      `?xs. st'.storage_trace = st1.storage_trace ++ xs` by
        metis_tac[storage_trace_frame_prefix, cj 5 evaluate_storage_trace_frame] >>
      `storage_observations_ok cx H st1.storage_trace` by
        metis_tac[storage_observations_ok_prefix] >>
      `storage_well_formed_on cx st1 (FST H)` by
        (qpat_x_assum `!env ty st res st'. _` drule_all >> simp[]) >>
      `runtime_consistent env cx st1` by
        (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
         drule_all (cj 1 (SPEC_ALL (cj 8 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual))) >>
         simp[]) >>
      qpat_x_assum `!env st res st'. _` drule_all >>
      disch_then (mp_tac o CONJUNCT1) >> simp[]) >>
  rename1 `eval_expr cx e st1 = (INL pv,st2)` >>
  Cases_on `read_result cx pv st2` >>
  rename1 `read_result cx pv st2 = (read_res,read_st)` >>
  reverse (Cases_on `read_res`)
  >- (qpat_assum `read_result cx pv st2 = (INR _,_)`
        (fn th => pure_rewrite_tac[th]) >>
      simp_tac(srw_ss())[] >> strip_tac >>
      gvs[AllCaseEqs()] >> drule read_result_state >> strip_tac >> gvs[] >>
      `?xs. read_st.storage_trace = st1.storage_trace ++ xs` by
        metis_tac[storage_trace_frame_prefix, cj 5 evaluate_storage_trace_frame] >>
      `storage_observations_ok cx H st1.storage_trace` by
        metis_tac[storage_observations_ok_prefix] >>
      `storage_well_formed_on cx st1 (FST H)` by
        (qpat_x_assum `!env ty st res st'. _` drule_all >> simp[]) >>
      `runtime_consistent env cx st1` by
        (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
         drule_all (cj 1 (SPEC_ALL (cj 8 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual))) >> simp[]) >>
      qpat_x_assum `!env st res st'. _` drule_all >>
      disch_then (mp_tac o CONJUNCT1) >> simp[]) >>
  qpat_assum `read_result cx pv st2 = (INL _,_)`
    (fn th => pure_rewrite_tac[th]) >>
  simp_tac(srw_ss())[] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule read_result_state >> strip_tac >> gvs[] >>
  `?xs. st'.storage_trace = read_st.storage_trace ++ xs` by
    metis_tac[storage_trace_frame_prefix, storage_trace_frame_append_place] >>
  `storage_observations_ok cx H read_st.storage_trace` by
    metis_tac[storage_observations_ok_prefix] >>
  `?ys. read_st.storage_trace = st1.storage_trace ++ ys` by
    metis_tac[storage_trace_frame_prefix, cj 5 evaluate_storage_trace_frame] >>
  `storage_observations_ok cx H st1.storage_trace` by
    metis_tac[storage_observations_ok_prefix] >>
  `storage_well_formed_on cx st1 (FST H)` by
    (qpat_x_assum `!env ty st res st'. _` drule_all >> simp[]) >>
  `runtime_consistent env cx st1` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_all (cj 1 (SPEC_ALL (cj 8 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual))) >> simp[]) >>
  `storage_well_formed_on cx read_st (FST H)` by
    (qpat_x_assum `!env st res st'. _` drule_all >>
     disch_then (mp_tac o CONJUNCT1) >> simp[]) >>
  qpat_x_assum `!env ty st res st'. _` kall_tac >>
  qpat_x_assum `!env st res st'. _` kall_tac >>
  drule_all eval_target_place_success_storage_type >> strip_tac >>
  drule_all eval_expr_success_storage_facts >> strip_tac >>
  `typed_scope_transition st1 read_st` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     qspecl_then [`cx`,`e`] strip_assume_tac
       (cj 5 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual) >>
     qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
       (qspecl_then [`env`,`st1`,`INL pv`,`read_st`] mp_tac) >> simp[]) >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame st1 read_st` by
    (drule (cj 5 vyperImmutableMetadataFrameTheory.eval_metadata_frame_mutual) >> simp[]) >>
  `?elem_tv. evaluate_type env.type_defs elem_ty = SOME elem_tv /\
     runtime_place_typed cx st1 p (ArrayTV elem_tv (Dynamic n))` by
    gvs[vyperTypeInvariantsTheory.eval_result_typed_def, evaluate_type_def, AllCaseEqs()] >>
  `runtime_place_typed cx read_st p (ArrayTV elem_tv (Dynamic n))` by
    (drule_all vyperTypeEvalSoundnessTheory.runtime_place_typed_transport >> simp[]) >>
  `value_runtime_typed env (expr_type e) x` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_all vyperTypeEvalSoundnessTheory.read_live_result_success_type >> simp[]) >>
  `value_runtime_typed env elem_ty x` by
    (gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
     drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >> strip_tac >> gvs[]) >>
  `value_has_type elem_tv x` by
    gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  irule append_place_preserves_storage_well_formed_on >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  qexistsl [`elem_tv`,`n`,`st1.storage_trace`] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`p`,`res`,`read_st`] >> simp[] >>
  rpt strip_tac >> gvs[] >>
  drule eval_target_place_observed_region >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[Assign_Tuple]:
  rpt gen_tac >> strip_tac >>
  rename1 `eval_stmt cx (Assign (TupleTarget gs) e) st = (res,st')` >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def, atarget_accepts_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_stmt _)` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (er,s1)` >>
  reverse (Cases_on `er`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> gvs[] >>
      qpat_x_assum `!s0 tv t s1 v t1. _` kall_tac >>
      first_x_assum drule_all >> disch_then (mp_tac o CONJUNCT1) >> simp[]) >>
  simp_tac(srw_ss())[] >>
  Cases_on `read_result cx x s1` >>
  rename1 `read_result cx x s1 = (mr,s2)` >>
  drule read_result_state >> strip_tac >> gvs[] >>
  reverse (Cases_on `mr`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> gvs[AllCaseEqs()] >>
      qpat_x_assum `!s0 tv t s1 v t1. _` kall_tac >>
      first_x_assum drule_all >> disch_then (mp_tac o CONJUNCT1) >> simp[]) >>
  simp_tac(srw_ss())[] >> strip_tac >> gvs[AllCaseEqs()] >>
  `?xs. st'.storage_trace = s1.storage_trace ++ xs` by
    metis_tac[storage_trace_frame_prefix, cj 9 evaluate_storage_trace_frame] >>
  `storage_observations_ok cx H s1.storage_trace` by
    metis_tac[storage_observations_ok_prefix] >>
  `storage_well_formed_on cx s1 (FST H)` by
    (qpat_x_assum `!env st res st'. _` drule_all >>
     disch_then (mp_tac o CONJUNCT1) >> simp[]) >>
  drule_all eval_expr_success_storage_facts >> strip_tac >>
  `value_runtime_typed env (expr_type e) x'` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_all vyperTypeEvalSoundnessTheory.read_live_result_success_type >> simp[]) >>
  qpat_x_assum `!s0 tv t s1 v t1. _` (drule_all_then strip_assume_tac) >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[Assign_Base]:
  rpt gen_tac >> strip_tac >>
  rename1 `eval_stmt cx (Assign (BaseTarget bt) e) st = (res,st')` >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  `?tty. well_typed_atarget env (BaseTarget bt) tty /\
         type_widens_to env.type_defs (expr_type e) tty /\
         assignable_type env.type_defs tty` by
    metis_tac[vyperTypeArgFitsTheory.atarget_accepts_well_typed_atarget] >>
  qpat_x_assum `well_typed_atarget env (BaseTarget bt) tty`
    (assume_tac o REWRITE_RULE [well_typed_atarget_def]) >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_stmt _)` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_atarget_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (rhs_res,rhs_st)` >>
  reverse (Cases_on `rhs_res`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> gvs[] >>
      qpat_x_assum `!s pv t. eval_expr _ _ _ = _ ==> _` kall_tac >>
      first_x_assum drule_all >> disch_then (mp_tac o CONJUNCT1) >> simp[]) >>
  qpat_x_assum `!s pv t. eval_expr _ _ _ = _ ==> _`
    (drule_then strip_assume_tac) >>
  simp_tac(srw_ss())[] >>
  Cases_on `eval_target_place cx bt rhs_st` >>
  rename1 `eval_target_place cx bt rhs_st = (target_res,target_st)` >>
  reverse (Cases_on `target_res`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> gvs[] >>
      `?xs. st'.storage_trace = rhs_st.storage_trace ++ xs` by
        metis_tac[storage_trace_frame_prefix, cj 8 evaluate_storage_trace_frame] >>
      `storage_observations_ok cx H rhs_st.storage_trace` by
        metis_tac[storage_observations_ok_prefix] >>
      `storage_well_formed_on cx rhs_st (FST H)` by
        (qpat_x_assum `!env st res st'. _` drule_all >>
         disch_then (mp_tac o CONJUNCT1) >> simp[]) >>
      drule_all eval_expr_success_storage_facts >> strip_tac >>
      qpat_x_assum `!env ty st res st'. _` drule_all >> simp[]) >>
  simp_tac(srw_ss())[] >>
  Cases_on `read_result cx x target_st` >>
  rename1 `read_result cx x target_st = (read_res,read_st)` >>
  drule read_result_state >> strip_tac >> gvs[] >>
  reverse (Cases_on `read_res`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> gvs[AllCaseEqs()] >>
      `?xs. read_st.storage_trace = rhs_st.storage_trace ++ xs` by
        metis_tac[storage_trace_frame_prefix, cj 8 evaluate_storage_trace_frame] >>
      `storage_observations_ok cx H rhs_st.storage_trace` by
        metis_tac[storage_observations_ok_prefix] >>
      `storage_well_formed_on cx rhs_st (FST H)` by
        (qpat_x_assum `!env st res st'. _` drule_all >>
         disch_then (mp_tac o CONJUNCT1) >> simp[]) >>
      drule_all eval_expr_success_storage_facts >> strip_tac >>
      qpat_x_assum `!env ty st res st'. _` drule_all >> simp[]) >>
  simp_tac(srw_ss())[] >> strip_tac >> gvs[AllCaseEqs()] >>
  `?xs. st'.storage_trace = read_st.storage_trace ++ xs` by
    metis_tac[storage_trace_frame_prefix, storage_trace_frame_write_place] >>
  `storage_observations_ok cx H read_st.storage_trace` by
    metis_tac[storage_observations_ok_prefix] >>
  `?ys. read_st.storage_trace = rhs_st.storage_trace ++ ys` by
    metis_tac[storage_trace_frame_prefix, cj 8 evaluate_storage_trace_frame] >>
  `storage_observations_ok cx H rhs_st.storage_trace` by
    metis_tac[storage_observations_ok_prefix] >>
  `storage_well_formed_on cx rhs_st (FST H)` by
    (qpat_x_assum `!env st res st'. _` drule_all >>
     disch_then (mp_tac o CONJUNCT1) >> simp[]) >>
  drule_all eval_expr_success_storage_facts >> strip_tac >>
  `storage_well_formed_on cx read_st (FST H)` by
    (qpat_x_assum `!env ty st res st'. _` drule_all >> simp[]) >>
  qpat_x_assum `!env ty st res st'. _` kall_tac >>
  qpat_x_assum `!env st res st'. _` kall_tac >>
  drule_all eval_target_place_success_storage_type >> strip_tac >>
  `typed_scope_transition rhs_st read_st` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_all (cj 2 (SPEC_ALL (cj 8 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual))) >> simp[]) >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame rhs_st read_st` by
    (drule (cj 8 vyperImmutableMetadataFrameTheory.eval_metadata_frame_mutual) >> simp[]) >>
  `live_memory_result read_st x` by
    metis_tac[vyperTypeEvalSoundnessTheory.live_result_transport] >>
  `eval_result_typed (env,cx,read_st) x (Type (expr_type e))` by
    (Cases_on `x` >> gvs[vyperTypeInvariantsTheory.eval_result_typed_def] >>
     drule_all vyperTypeEvalSoundnessTheory.runtime_place_typed_transport >> simp[]) >>
  `runtime_consistent env cx read_st` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_all (cj 1 (SPEC_ALL (cj 8 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual))) >> simp[]) >>
  `value_runtime_typed env (expr_type e) x''` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_all vyperTypeEvalSoundnessTheory.read_live_result_success_type >> simp[]) >>
  `value_runtime_typed env tty x''` by
    (gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
     drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >> strip_tac >> gvs[]) >>
  gvs[vyperTypeInvariantsTheory.eval_result_typed_def,
      vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  irule write_place_preserves_storage_well_formed_on >>
  goal_assum (drule_at Any) >>
  qexistsl [`tv'`,`read_st.storage_trace`,`x'`,`res`,`read_st`,`x''`] >> simp[] >>
  rpt strip_tac >> gvs[] >>
  drule eval_target_place_observed_region >> simp[]
QED


Resume eval_storage_well_formed_on_mutual[Expr_Pop]:
  rpt gen_tac >> strip_tac >>
  rename1 `eval_expr cx (Pop elem_ty bt) st = (res,st')` >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    gvs[int_calls_expr_def] >>
  conj_tac
  >- (strip_tac >>
      drule vyperTypeAssignContextTheory.well_typed_expr_Pop_dynamic_target >> strip_tac >>
      `well_typed_target env bt (ArrayT elem_ty (Dynamic n))` by
        simp[well_typed_target_def] >>
      qpat_x_assum `eval_expr cx (Pop _ bt) st = _` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
      Cases_on `eval_target_place cx bt st` >>
      rename1 `eval_target_place cx bt st = (target_res,middle)` >>
      reverse (Cases_on `target_res`)
      >- (simp_tac(srw_ss())[] >> strip_tac >> gvs[] >>
          first_x_assum drule_all >> simp[]) >>
      simp_tac(srw_ss())[] >> strip_tac >>
      `?xs. st'.storage_trace = middle.storage_trace ++ xs` by
        metis_tac[storage_trace_frame_prefix, storage_trace_frame_pop_place] >>
      `storage_observations_ok cx H middle.storage_trace` by
        metis_tac[storage_observations_ok_prefix] >>
      `storage_well_formed_on cx middle (FST H)` by
        (first_x_assum drule_all >> simp[]) >>
      qpat_x_assum `!env ty st res st'. _` kall_tac >>
      drule_all eval_target_place_success_storage_type >> strip_tac >>
      gvs[vyperTypeInvariantsTheory.eval_result_typed_def,
          evaluate_type_def, AllCaseEqs()] >>
      irule pop_place_preserves_storage_well_formed_on >>
      conj_tac >- (first_assum ACCEPT_TAC) >>
      qexistsl [`tv'`,`n`,`middle.storage_trace`] >>
      goal_assum (drule_at Any) >> simp[] >>
      rpt strip_tac >> gvs[] >>
      drule eval_target_place_observed_region >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_storage_well_formed_on_mutual[AugAssign]:
  rpt gen_tac >> strip_tac >>
  rename1 `eval_stmt cx (AugAssign ty bt bop e) st = (res,st')` >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_stmt _)` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_target_place cx bt st` >>
  rename1 `eval_target_place cx bt st = (target_res,target_st)` >>
  reverse (Cases_on `target_res`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> gvs[] >>
      qpat_x_assum `!env ty st res st'. _` drule_all >> simp[]) >>
  simp_tac(srw_ss())[] >>
  Cases_on `read_place cx x target_st` >>
  rename1 `read_place cx x target_st = (read_res,read_st)` >>
  drule read_place_state >> strip_tac >> gvs[] >>
  rename1 `eval_target_place cx bt st = (INL x,target_st)` >>
  reverse (Cases_on `read_res`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> gvs[] >>
      qpat_x_assum `!env ty st res st'. _` drule_all >> simp[]) >>
  simp_tac(srw_ss())[] >>
  Cases_on `place_type_value cx x target_st` >>
  rename1 `place_type_value cx x target_st = (type_res,type_st)` >>
  drule place_type_value_state >> strip_tac >> gvs[] >>
  reverse (Cases_on `type_res`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> gvs[] >>
      qpat_x_assum `!env ty st res st'. _` drule_all >> simp[]) >>
  simp_tac(srw_ss())[] >>
  qpat_x_assum `!s p t r v u a tv b. eval_target_place _ _ _ = _ /\ _ ==> _`
    (drule_at_then (Pat `eval_target_place _ _ _ = _`) mp_tac) >>
  simp[] >> disch_then drule >> simp[] >> disch_then drule >>
  strip_tac >>
  Cases_on `eval_expr cx e target_st` >>
  rename1 `eval_expr cx e target_st = (rhs_res,rhs_st)` >>
  reverse (Cases_on `rhs_res`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> gvs[] >>
      `?xs. rhs_st.storage_trace = target_st.storage_trace ++ xs` by
        metis_tac[storage_trace_frame_prefix, cj 5 evaluate_storage_trace_frame] >>
      `storage_observations_ok cx H target_st.storage_trace` by
        metis_tac[storage_observations_ok_prefix] >>
      `storage_well_formed_on cx target_st (FST H)` by
        (qpat_x_assum `!env ty st res st'. _` drule_all >> simp[]) >>
      `runtime_consistent env cx target_st` by
        (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
         drule_all (cj 1 (SPEC_ALL (cj 8 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual))) >> simp[]) >>
      qpat_x_assum `!env st res st'. _` drule_all >>
      disch_then (mp_tac o CONJUNCT1) >> simp[]) >>
  simp_tac(srw_ss())[] >>
  Cases_on `read_result cx x''' rhs_st` >>
  rename1 `read_result cx x''' rhs_st = (delayed_res,delayed_st)` >>
  drule read_result_state >> strip_tac >> gvs[] >>
  rename1 `eval_expr cx e target_st = (INL pv,rhs_st)` >>
  reverse (Cases_on `delayed_res`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> gvs[] >>
      rename1 `eval_expr cx e target_st = (INL pv,rhs_st)` >>
      `?xs. rhs_st.storage_trace = target_st.storage_trace ++ xs` by
        metis_tac[storage_trace_frame_prefix, cj 5 evaluate_storage_trace_frame] >>
      `storage_observations_ok cx H target_st.storage_trace` by
        metis_tac[storage_observations_ok_prefix] >>
      `storage_well_formed_on cx target_st (FST H)` by
        (qpat_x_assum `!env ty st res st'. _` drule_all >> simp[]) >>
      `runtime_consistent env cx target_st` by
        (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
         drule_all (cj 1 (SPEC_ALL (cj 8 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual))) >> simp[]) >>
      qpat_x_assum `!env st res st'. _` drule_all >>
      disch_then (mp_tac o CONJUNCT1) >> simp[]) >>
  simp_tac(srw_ss())[lift_sum_def, bind_def] >>
  qmatch_goalsub_abbrev_tac `evaluate_binop bound ptv bop cur right` >>
  reverse (Cases_on `evaluate_binop bound ptv bop cur right`)
  >- (simp_tac(srw_ss())[return_def, raise_def] >> strip_tac >> gvs[] >>
      rename1 `eval_expr cx e target_st = (INL pv,rhs_st)` >>
      `?xs. rhs_st.storage_trace = target_st.storage_trace ++ xs` by
        metis_tac[storage_trace_frame_prefix, cj 5 evaluate_storage_trace_frame] >>
      `storage_observations_ok cx H target_st.storage_trace` by
        metis_tac[storage_observations_ok_prefix] >>
      `storage_well_formed_on cx target_st (FST H)` by
        (qpat_x_assum `!env ty st res st'. _` drule_all >> simp[]) >>
      `runtime_consistent env cx target_st` by
        (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
         drule_all (cj 1 (SPEC_ALL (cj 8 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual))) >> simp[]) >>
      qpat_x_assum `!env st res st'. _` drule_all >>
      disch_then (mp_tac o CONJUNCT1) >> simp[]) >>
  simp_tac(srw_ss())[return_def, raise_def] >> strip_tac >> gvs[] >>
  `?xs. st'.storage_trace = rhs_st.storage_trace ++ xs` by
    metis_tac[storage_trace_frame_prefix, storage_trace_frame_write_place] >>
  `storage_observations_ok cx H rhs_st.storage_trace` by
    metis_tac[storage_observations_ok_prefix] >>
  `?ys. rhs_st.storage_trace = target_st.storage_trace ++ ys` by
    metis_tac[storage_trace_frame_prefix, cj 5 evaluate_storage_trace_frame] >>
  `storage_observations_ok cx H target_st.storage_trace` by
    metis_tac[storage_observations_ok_prefix] >>
  `storage_well_formed_on cx target_st (FST H)` by
    (qpat_x_assum `!env ty st res st'. _` drule_all >> simp[]) >>
  `runtime_consistent env cx target_st` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_all (cj 1 (SPEC_ALL (cj 8 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual))) >> simp[]) >>
  `storage_well_formed_on cx rhs_st (FST H)` by
    (qpat_x_assum `!env st res st'. _` drule_all >>
     disch_then (mp_tac o CONJUNCT1) >> simp[]) >>
  qpat_x_assum `!env ty st res st'. _` kall_tac >>
  qpat_x_assum `!env st res st'. _` kall_tac >>
  drule_all eval_target_place_success_storage_type >> strip_tac >>
  `live_memory_result target_st (PlaceR x)` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_all (cj 3 (SPEC_ALL (cj 8 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual))) >> simp[]) >>
  `?tv. evaluate_type env.type_defs ty = SOME tv /\
        runtime_place_typed cx target_st x tv` by
    gvs[vyperTypeInvariantsTheory.eval_result_typed_def] >>
  `ptv = tv` by
    (fs[vyperTypeInvariantsTheory.runtime_place_typed_def] >> gvs[]) >>
  gvs[] >>
  `value_has_type ptv cur` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_all vyperTypeEvalSoundnessTheory.live_place_read_sound >> simp[]) >>
  drule_all eval_expr_success_storage_facts >> strip_tac >>
  `value_runtime_typed env (expr_type e) right` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_all vyperTypeEvalSoundnessTheory.read_live_result_success_type >> simp[]) >>
  `typed_scope_transition target_st rhs_st` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     qspecl_then [`cx`,`e`] strip_assume_tac
       (cj 5 vyperTypeEvalSoundnessTheory.eval_scc_type_sound_mutual) >>
     qpat_x_assum `!env st res st'. _ ==> typed_scope_transition _ _`
       (qspecl_then [`env`,`target_st`,`INL pv`,`rhs_st`] mp_tac) >> simp[]) >>
  `vyperImmutableMetadataFrame$immutable_metadata_frame target_st rhs_st` by
    (drule (cj 5 vyperImmutableMetadataFrameTheory.eval_metadata_frame_mutual) >> simp[]) >>
  `runtime_place_typed cx rhs_st x ptv` by
    (drule_all vyperTypeEvalSoundnessTheory.runtime_place_typed_transport >> simp[]) >>
  rename1 `evaluate_binop bound ptv bop cur right = INL updated` >>
  `value_has_type ptv updated` by
    (fs[vyperTypeExprSoundnessTheory.value_runtime_typed_def, Abbr `bound`] >>
     irule vyperTypeBuiltinsTheory.well_typed_binop_success_type >>
     goal_assum (drule_at (Pat `evaluate_binop _ _ _ _ _ = _`)) >>
     simp[] >> goal_assum (drule_at (Pat `well_typed_binop _ _ _ _`)) >> simp[] >>
     qexists_tac `env.type_defs` >> simp[]) >>
  irule write_place_preserves_storage_well_formed_on >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  qexistsl [`ptv`,`target_st.storage_trace`] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`x`,`res`,`rhs_st`] >> simp[] >>
  rpt strip_tac >> gvs[] >>
  drule eval_target_place_observed_region >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[AssertCustomError]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Assert e (AssertCustomError err)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def, well_typed_custom_error_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,st1)` >>
  reverse (Cases_on `er`)
  >- (qpat_x_assum `!s tv t id positional kwargs tops params es. _` kall_tac >>
      simp_tac(srw_ss())[] >> rpt strip_tac >> gvs[] >>
      first_x_assum drule_all >> simp[]) >>
  simp_tac(srw_ss())[switch_BoolV_def, bind_def, return_def, raise_def] >>
  qpat_x_assum `!s tv t id positional kwargs tops params es. _`
    (drule_at (Pat `eval_expr _ _ _ = _`)) >> strip_tac >>
  Cases_on `read_result cx x st1` >> rename1 `read_result cx x st1 = (rr,st2)` >>
  `st2 = st1` by metis_tac[read_result_state] >> BasicProvers.VAR_EQ_TAC >>
  reverse (Cases_on `rr`) >> simp_tac(srw_ss())[]
  >- (rpt strip_tac >> BasicProvers.VAR_EQ_TAC >> first_x_assum drule_all >> simp[]) >>
  Cases_on `x' = BoolV T` >>
  pop_assum (fn th => rewrite_tac[th, return_def, raise_def]) >>
  simp_tac(srw_ss())[]
  >- (rpt strip_tac >> BasicProvers.VAR_EQ_TAC >> first_x_assum drule_all >> simp[]) >>
  reverse (Cases_on `x' = BoolV F`) >>
  pop_assum (fn th => rewrite_tac[th, return_def, raise_def]) >>
  simp_tac(srw_ss())[]
  >- (rpt strip_tac >> BasicProvers.VAR_EQ_TAC >> first_x_assum drule_all >> simp[]) >>
  Cases_on `err` >> rename1 `CustomError id positional kwargs` >>
  simp_tac(srw_ss())[] >>
  Cases_on `get_module_code cx (FST id)`
  >- (simp_tac(srw_ss())[raise_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
      first_x_assum drule_all >> simp[]) >>
  rename1 `get_module_code cx (FST id) = SOME tops` >>
  simp_tac(srw_ss())[] >>
  Cases_on `lookup_custom_error_args_in (SND id) tops`
  >- (simp_tac(srw_ss())[raise_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
      first_x_assum drule_all >> simp[]) >>
  rename1 `lookup_custom_error_args_in (SND id) tops = SOME params` >>
  simp_tac(srw_ss())[] >>
  Cases_on `order_custom_error_args params (CustomError id positional kwargs)`
  >- (simp_tac(srw_ss())[raise_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
      first_x_assum drule_all >> simp[]) >>
  rename1 `order_custom_error_args params (CustomError id positional kwargs) = SOME es` >>
  simp_tac(srw_ss())[bind_def] >>
  `PERM (custom_error_exprs (CustomError id positional kwargs)) es` by
    (drule vyperASTTheory.order_custom_error_args_perm >> simp[]) >>
  `well_typed_exprs env es` by metis_tac[well_typed_exprs_perm] >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    metis_tac[call_evaluation_safe_exprs_perm] >>
  Cases_on `eval_exprs cx es st1` >> rename1 `eval_exprs cx es st1 = (ar,st3)` >>
  strip_tac >>
  `st' = st3` by
    (ntac 2 (qpat_x_assum `!env st res st'. _` kall_tac) >>
     Cases_on `ar` >> gvs[bind_def, raise_def, lift_option_def, return_def, AllCaseEqs()] >>
     Cases_on `build_custom_error_data (get_tenv cx) (SND id) (MAP SND params) x''` >>
     gvs[raise_def, return_def]) >>
  qpat_x_assum `st' = st3` SUBST_ALL_TAC >>
  `storage_observations_ok cx H st1.storage_trace` by
    (ntac 2 (qpat_x_assum `!a b c d. _` kall_tac) >>
     metis_tac[storage_trace_frame_prefix, cj 6 evaluate_storage_trace_frame,
               storage_observations_ok_prefix]) >>
  `storage_well_formed_on cx st1 (FST H)` by
    (first_x_assum drule_all >> disch_then (mp_tac o CONJUNCT1) >>
     disch_then drule >> simp_tac(srw_ss())[]) >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent] >>
  first_x_assum (drule_at (Pat `order_custom_error_args _ _ = _`)) >>
  simp_tac(srw_ss())[] >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[BasePlaceRoot_AttributeTarget]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_target _ (AttributeTarget _ _) = _` mp_tac >>
  simp[vyperTypeEnvTheory.type_place_target_AttributeTarget] >> strip_tac >>
  gvs[int_calls_expr_def] >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac extend_place_state >> gvs[] >>
  `storage_observations_ok cx H s''.storage_trace` by
    (qpat_x_assum `!env vt st res st'. _` kall_tac >>
     metis_tac[storage_trace_frame_prefix, storage_trace_frame_extend_place,
               storage_observations_ok_prefix]) >>
  first_x_assum drule_all >> simp_tac(srw_ss())[] >> strip_tac >>
  qpat_x_assum `st' = _` SUBST1_TAC >>
  gvs[storage_well_formed_on_def, get_storage_def]
QED

Resume eval_storage_well_formed_on_mutual[BasePlaceRoot_SubscriptTarget]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_target (SubscriptTarget bt e))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  drule call_evaluation_safe_append_left >> strip_tac >>
  drule call_evaluation_safe_append_right >> strip_tac >>
  qpat_x_assum `type_place_target _ (SubscriptTarget _ _) = _` mp_tac >>
  rewrite_tac[vyperTypeEnvTheory.type_place_target_SubscriptTarget] >> strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_place cx bt st` >> rename1 `eval_base_place cx bt st = (br,st1)` >>
  reverse (Cases_on `br`)
  >- (qpat_x_assum `!s pv t. eval_base_place cx bt s = (INL pv,t) ==> _` kall_tac >> simp_tac(srw_ss())[] >>
      strip_tac >> BasicProvers.VAR_EQ_TAC >> first_x_assum drule_all >> simp[]) >>
  qpat_x_assum `!s pv t. eval_base_place cx bt s = (INL pv,t) ==> _` (drule_at (Pat `eval_base_place _ _ _ = _`)) >> strip_tac >>
  simp_tac(srw_ss())[bind_def] >>
  Cases_on `eval_expr cx e st1` >> rename1 `eval_expr cx e st1 = (er,st2)` >>
  strip_tac >>
  `st'.accounts = st2.accounts /\ st'.tStorage = st2.tStorage /\
   storage_observations_ok cx H st2.storage_trace` by
    (ntac 2 (qpat_x_assum `!a b c d. _` kall_tac) >>
     Cases_on `er` >> gvs[AllCaseEqs()] >>
     imp_res_tac read_result_state >> gvs[] >>
     imp_res_tac extend_place_state >> gvs[] >>
     conj_tac >- (qpat_x_assum `st' = _` SUBST1_TAC >> simp[]) >>
     conj_tac >- (qpat_x_assum `st' = _` SUBST1_TAC >> simp[]) >>
     metis_tac[storage_trace_frame_prefix, storage_trace_frame_extend_place,
               storage_observations_ok_prefix]) >>
  `storage_observations_ok cx H st1.storage_trace` by
    (drule_all eval_expr_storage_observations_ok_input >> simp_tac(srw_ss())[]) >>
  `storage_well_formed_on cx st1 (FST H)` by (first_x_assum drule_all >> simp[]) >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_base_place_preserves_runtime_consistent] >>
  `storage_well_formed_on cx st2 (FST H)` by
    (first_x_assum drule_all >> disch_then (mp_tac o CONJUNCT1) >>
     disch_then drule >> simp_tac(srw_ss())[]) >>
  metis_tac[storage_well_formed_on_backends]
QED

Resume eval_storage_well_formed_on_mutual[Log]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Log id es))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def, AllCaseEqs()] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (er,st1)` >>
  Cases_on `er` >> simp_tac(srw_ss())[bind_def, return_def, push_log_def]
  >- (Cases_on `encode_source_event (get_tenv cx) cx.sources cx.txn.target id x` >>
      simp_tac(srw_ss())[lift_option_def, bind_def, raise_def, return_def, push_log_def] >>
      strip_tac >> BasicProvers.VAR_EQ_TAC >>
      gvs[] >> first_x_assum drule_all >> simp_tac(srw_ss())[] >> strip_tac >>
      irule (iffRL storage_well_formed_on_backends) >> qexists `st1` >> simp[]) >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >> first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[AnnAssign]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  `get_tenv cx = env.type_defs` by
    fs[vyperTypeExprSoundnessTheory.runtime_consistent_def,
       vyperTypeInvariantsTheory.env_consistent_def, vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `?tyv. evaluate_type env.type_defs typ = SOME tyv` by
    (drule assignable_type_well_formed >>
     simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >> asm_rewrite_tac[] >>
  qpat_x_assum `!tenv s tyv t. _`
    (qspecl_then [`env.type_defs`, `st`, `tyv`, `st`] mp_tac) >>
  simp_tac(srw_ss())[lift_option_type_def, return_def] >>
  asm_rewrite_tac[] >> strip_tac >>
  simp_tac(srw_ss())[bind_def, lift_option_type_def, return_def] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (er,st1)` >>
  qpat_x_assum `_ ==> !env st res st'. _` mp_tac >>
  simp_tac(srw_ss())[return_def] >> strip_tac >>
  simp_tac(srw_ss())[LET_THM, bind_def, return_def] >>
  qpat_assum `evaluate_type env.type_defs typ = SOME tyv`
    (fn th => rewrite_tac[th, return_def]) >>
  simp_tac(srw_ss())[bind_def, return_def] >>
  qpat_assum `eval_expr cx e st = _` (fn th => rewrite_tac[th]) >>
  reverse (Cases_on `er`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
      first_x_assum drule_all >> simp[]) >>
  simp_tac(srw_ss())[] >>
  Cases_on `read_result cx x st1` >> rename1 `read_result cx x st1 = (rr,st2)` >>
  `st2 = st1` by metis_tac[read_result_state] >> BasicProvers.VAR_EQ_TAC >>
  reverse (Cases_on `rr`)
  >- (simp_tac(srw_ss())[] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
      first_x_assum drule_all >> simp[]) >>
  simp_tac(srw_ss())[] >> strip_tac >>
  `storage_observations_ok cx H st1.storage_trace` by
    (qpat_x_assum `!env st res st'. _` kall_tac >>
     metis_tac[storage_trace_frame_prefix, storage_trace_frame_new_variable,
               storage_observations_ok_prefix]) >>
  `storage_well_formed_on cx st1 (FST H)` by
    (first_x_assum drule_all >> simp[]) >>
  `st'.accounts = st1.accounts /\ st'.tStorage = st1.tStorage` by
    (qpat_x_assum `new_variable _ _ _ _ = _` mp_tac >>
     Cases_on `st1.scopes` >>
     simp[new_variable_def, bind_def, ignore_bind_def, get_scopes_def, type_check_def,
          set_scopes_def, return_def, raise_def, assert_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[]) >>
  metis_tac[storage_well_formed_on_backends]
QED

Resume eval_storage_well_formed_on_mutual[Expr_Builtin]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Builtin ty bt es))` mp_tac >>
     pure_rewrite_tac[int_calls_expr_def] >> simp[]) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Builtin _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (Builtin ty bt es)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  `builtin_args_length_ok bt (LENGTH es)` by
    (drule vyperTypeBuiltinsTheory.well_typed_builtin_app_length >> simp[]) >>
  qpat_x_assum `eval_expr cx (Builtin ty bt es) st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def,
    type_check_def, assert_def] >>
  Cases_on `bt = Len`
  >- (`es <> []` by
        (Cases_on `es` >> simp[] >>
         qpat_x_assum `well_typed_builtin_app ty bt (MAP expr_type [])` mp_tac >>
         qpat_x_assum `bt = Len` (fn th => rewrite_tac[th]) >>
         simp[well_typed_builtin_app_def]) >>
      `call_evaluation_safe cx (int_calls_expr (HD es))` by
        (Cases_on `es` >> gvs[int_calls_expr_def] >>
         drule call_evaluation_safe_append_left >> simp[]) >>
      `well_typed_expr env (HD es)` by
        (Cases_on `es` >> gvs[well_typed_expr_def]) >>
      qpat_assum `builtin_args_length_ok bt (LENGTH es)` (fn th => rewrite_tac[th]) >>
      qpat_assum `bt = Len` (fn th => rewrite_tac[th]) >>
      simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
        type_check_def, assert_def] >>
      qpat_x_assum `!s x t. _ /\ bt = Len ==> _`
        (qspecl_then [`st`, `()`, `st`] mp_tac) >>
      simp_tac(srw_ss())[type_check_def, assert_def, return_def] >>
      asm_rewrite_tac[] >> strip_tac >>
      Cases_on `eval_expr cx (HD es) st` >>
      rename1 `eval_expr cx (HD es) st = (ar,ast)` >>
      Cases_on `ar` >> simp_tac(srw_ss())[]
      >- (Cases_on `result_array_length cx x ast` >>
          imp_res_tac vyperStatePreservationTheory.result_array_length_state >> gvs[] >>
          Cases_on `q` >> simp_tac(srw_ss())[return_def, raise_def] >>
          strip_tac >> BasicProvers.VAR_EQ_TAC >> first_x_assum drule_all >> simp[]) >>
      strip_tac >> BasicProvers.VAR_EQ_TAC >> first_x_assum drule_all >> simp[]) >>
  qpat_x_assum `!s x t. _ /\ bt = Len ==> _` kall_tac >>
  Cases_on `bt = Env MsgGas`
  >- (qpat_x_assum `!s x t. _` kall_tac >>
      rpt strip_tac >>
      gvs[ignore_bind_def, assert_def, bind_def, return_def] >>
      Cases_on `next_gas_reading st` >>
      imp_res_tac vyperStatePreservationTheory.next_gas_reading_state >>
      Cases_on `q` >> gvs[return_def, raise_def] >>
      irule (iffRL storage_well_formed_on_backends) >> qexists `st` >> simp[]) >>
  qpat_assum `bt <> Len` (fn th => rewrite_tac[th]) >>
  qpat_assum `bt <> Env MsgGas` (fn th => rewrite_tac[th]) >>
  qpat_assum `builtin_args_length_ok bt (LENGTH es)` (fn th => rewrite_tac[th]) >>
  simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
    type_check_def, assert_def, get_accounts_def, lift_sum_def] >>
  qpat_x_assum `!s x t. _`
    (qspecl_then [`st`, `()`, `st`] mp_tac) >>
  simp_tac(srw_ss())[type_check_def, assert_def, return_def] >>
  asm_rewrite_tac[] >> strip_tac >>
  Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (ar,ast)` >>
  Cases_on `ar` >> simp_tac(srw_ss())[]
  >- (Cases_on `evaluate_builtin cx ast.accounts ty bt (MAP expr_type es) x` >>
      simp_tac(srw_ss())[return_def, raise_def]
      >- (Cases_on `precompile_call_success bt ast` >>
          rename1 `precompile_call_success bt ast = (pr,pst)` >>
          drule vyperStatePreservationTheory.precompile_call_success_state >>
          strip_tac >> Cases_on `pr` >> gvs[] >>
          strip_tac >> BasicProvers.VAR_EQ_TAC >>
          irule (iffRL storage_well_formed_on_backends) >> qexists `ast` >>
          simp_tac(srw_ss())[] >> fs[] >> first_x_assum drule_all >> simp[]) >>
      strip_tac >> BasicProvers.VAR_EQ_TAC >> first_x_assum drule_all >> simp[]) >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >> first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[Expr_Subscript]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e) /\
   call_evaluation_safe cx (int_calls_expr e')` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Subscript v8 e e'))` mp_tac >>
     pure_rewrite_tac[int_calls_expr_def] >>
     metis_tac[call_evaluation_safe_append_left, call_evaluation_safe_append_right]) >>
  `(well_typed_expr env (Subscript v8 e e') \/
    ?vt. type_place_expr env (Subscript v8 e e') = SOME vt) ==>
    storage_well_formed_on cx st' (FST H)` suffices_by metis_tac[] >>
  disch_tac >>
  `well_typed_expr env e' /\
   (well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt)` by
    (qpat_x_assum `_ \/ _` mp_tac >>
     simp_tac(srw_ss())[Ntimes well_typed_expr_def 2, AllCaseEqs()] >> metis_tac[]) >>
  (qpat_x_assum `eval_expr cx (Subscript v8 e e') st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (br,st1)` >>
  reverse (Cases_on `br`) >> simp_tac(srw_ss())[return_def, raise_def]
  >- (strip_tac >> BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `!s pv t. eval_expr cx e s = (INL pv,t) ==> _` kall_tac >>
      first_x_assum drule_all >> strip_tac >> metis_tac[]) >>
  Cases_on `eval_expr cx e' st1` >>
  rename1 `eval_expr cx e' st1 = (ir,st2)` >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent,
              eval_expr_place_preserves_runtime_consistent] >>
  qpat_x_assum `!s pv t. eval_expr cx e s = (INL pv,t) ==> _`
    (qspecl_then [`st`, `x`, `st1`] mp_tac) >>
  asm_rewrite_tac[] >> strip_tac >> strip_tac >>
  `st'.accounts = st2.accounts /\ st'.tStorage = st2.tStorage /\
   storage_observations_ok cx H st2.storage_trace` by
    (ntac 2 (qpat_x_assum `!a b c d. _` kall_tac) >>
     Cases_on `ir` >> gvs[AllCaseEqs()] >>
     imp_res_tac read_result_state >> gvs[] >>
     imp_res_tac vyperPlaceFramesTheory.select_result_state >> gvs[] >>
     qpat_x_assum `st' = _` SUBST1_TAC >> simp_tac(srw_ss())[] >>
     metis_tac[storage_trace_frame_prefix, storage_trace_frame_select,
               storage_observations_ok_prefix]) >>
  `storage_observations_ok cx H st1.storage_trace` by
    (drule_all eval_expr_storage_observations_ok_input >> simp_tac(srw_ss())[]) >>
  `storage_well_formed_on cx st1 (FST H)` by
    (qpat_x_assum `!a b c d. _ ==> (well_typed_expr a e ==> _) /\ _` drule_all >>
     strip_tac >> metis_tac[]) >>
  `storage_well_formed_on cx st2 (FST H)` by
    (first_x_assum drule_all >> disch_then (mp_tac o CONJUNCT1) >>
     disch_then drule >> simp_tac(srw_ss())[]) >>
  metis_tac[storage_well_formed_on_backends])
QED

Resume eval_storage_well_formed_on_mutual[For]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_iterator it) /\
   call_evaluation_safe cx (int_calls_stmts body')` by
    (qpat_assum `call_evaluation_safe cx (int_calls_stmt (For id typ it n body'))` mp_tac >>
     pure_rewrite_tac[int_calls_stmt_def] >>
     metis_tac[call_evaluation_safe_append_left, call_evaluation_safe_append_right]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  `env.type_defs = get_tenv cx` by
    metis_tac[vyperTypeExtCallCoreTheory.runtime_consistent_get_tenv] >>
  `?env_after. type_stmts (extend_local env id typ F) ret_ty body' = SOME env_after` by
    (qpat_x_assum `IS_SOME (type_stmts _ _ _)` mp_tac >>
     rewrite_tac[optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, lift_option_type_def,
    check_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `evaluate_type (get_tenv cx) typ` >> gvs[]
  >- (rpt strip_tac >> gvs[bind_def, return_def, raise_def]) >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME iter_tyv` >>
  Cases_on `eval_iterator cx it st` >>
  rename1 `eval_iterator cx it st = (ir,st1)` >>
  qpat_x_assum `case it of Array _ => _ | Range _ _ => _` kall_tac >>
  reverse (Cases_on `ir`) >>
  simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def] >>
  qpat_assum `eval_iterator cx it st = _` (fn th => rewrite_tac[th]) >>
  simp_tac(srw_ss())[]
  >- (strip_tac >> BasicProvers.VAR_EQ_TAC >>
      qpat_x_assum `!a b c d e. _ /\ check _ _ _ = _ ==> _` kall_tac >>
      first_x_assum drule_all >> simp[]) >>
  rename1 `eval_iterator cx it st = (INL vs,st1)` >>
  Cases_on `compatible_bound (Dynamic n) (LENGTH vs)` >>
  simp_tac(srw_ss())[check_def, assert_def, bind_def, ignore_bind_def,
                      return_def, raise_def] >> asm_rewrite_tac[]
  >- (strip_tac >>
      `storage_observations_ok cx H st1.storage_trace` by
        (qpat_x_assum `!a b c d e. _ /\ check _ _ _ = _ ==> _` kall_tac >>
         qpat_x_assum `!a b c d e. _` kall_tac >>
         gvs[] >>
         `?suffix. st'.storage_trace = st1.storage_trace ++ suffix` by
           (irule (INST_TYPE [alpha |-> ``:unit``] storage_trace_frame_prefix) >>
            qexistsl [`eval_for cx iter_tyv id body' vs`, `res`] >>
            simp_tac(srw_ss())[cj 4 evaluate_storage_trace_frame] >>
            first_assum ACCEPT_TAC) >>
         metis_tac[storage_observations_ok_prefix]) >>
      `storage_well_formed_on cx st1 (FST H)` by
        (qpat_x_assum `!a b c d e. _ /\ check _ _ _ = _ ==> _` kall_tac >>
         first_x_assum drule_all >> simp[]) >>
      `runtime_consistent env cx st1` by
        (fs[runtime_consistent_def] >>
         drule_all (cj 3 eval_scc_type_sound_mutual) >> simp[]) >>
      `EVERY (value_has_type iter_tyv) vs` by
        (fs[runtime_consistent_def] >>
         drule_all (cj 3 eval_scc_type_sound_mutual) >> simp[]) >>
      qpat_x_assum `!a b c d e. _ /\ check _ _ _ = _ ==> _`
        (qspecl_then [`st`, `vs`, `st1`, `st1`, `st1`] mp_tac) >>
      asm_rewrite_tac[] >>
      simp_tac(srw_ss())[check_def, assert_def, return_def] >>
      strip_tac >> fs[] >>
      first_x_assum (qspec_then `env` mp_tac) >> asm_rewrite_tac[] >>
      strip_tac >> first_x_assum drule_all >> simp[]) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `!a b c d e. _ /\ check _ _ _ = _ ==> _` kall_tac >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[For_cons]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_for _ _ _ _ (_::_) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
    push_scope_with_var_def, return_def] >>
  qmatch_goalsub_abbrev_tac `finally loop_body pop_scope stp` >>
  Cases_on `finally loop_body pop_scope stp` >>
  rename1 `finally loop_body pop_scope stp = (lr,st_after)` >> strip_tac >>
  `push_scope_with_var id tyv v st = (INL (),stp)` by
    simp[push_scope_with_var_def, return_def, Abbr `stp`] >>
  qunabbrev_tac `loop_body` >>
  drule_all (SRULE [ignore_bind_def] pushed_loop_cleanup) >> strip_tac >>
  `value_has_type tyv v` by fs[] >>
  `runtime_consistent (extend_local env id ty F) cx stp` by
    (drule_all push_loop_runtime_consistent >> simp[]) >>
  `storage_well_formed_on cx stp (FST H)` by
    (irule (iffRL storage_well_formed_on_backends) >> qexists `st` >>
     simp[Abbr `stp`]) >>
  `storage_observations_ok cx H st_after.storage_trace` by
    (qpat_x_assum `!a b c. push_scope_with_var _ _ _ _ = _ ==> _` kall_tac >>
     qpat_x_assum `!a b c d e f. _ /\ finally _ _ _ = _ /\ _ ==> _` kall_tac >>
     qpat_x_assum `st_after = _` kall_tac >>
     Cases_on `lr` >> simp_tac(srw_ss())[] >>
     gvs[return_def, AllCaseEqs()] >>
     Cases_on `x` >> gvs[return_def] >>
     `?suffix. st'.storage_trace = st_after.storage_trace ++ suffix` by
       (irule (INST_TYPE [alpha |-> ``:unit``] storage_trace_frame_prefix) >>
        qexistsl [`eval_for cx tyv id body' vs`, `res`] >>
        simp_tac(srw_ss())[cj 4 evaluate_storage_trace_frame] >>
        first_assum ACCEPT_TAC) >>
     metis_tac[storage_observations_ok_prefix]) >>
  `storage_observations_ok cx H st_body.storage_trace` by
    (qpat_assum `st_after = _` (fn th => fs[th])) >>
  `storage_well_formed_on cx st_body (FST H)` by
    (qpat_x_assum `!a b c d e f. _ /\ finally _ _ _ = _ /\ _ ==> _` kall_tac >>
     qpat_x_assum `!a b c. push_scope_with_var _ _ _ _ = _ ==> _`
       (qspecl_then [`st`, `()`, `stp`] mp_tac) >>
     asm_rewrite_tac[] >> strip_tac >> first_x_assum drule_all >> simp[]) >>
  `storage_well_formed_on cx st_after (FST H)` by
    (irule (iffRL storage_well_formed_on_backends) >> qexists `st_body` >>
     qpat_assum `st_after = _` (fn th => simp[th])) >>
  qpat_x_assum `!a b c. push_scope_with_var _ _ _ _ = _ ==> _` kall_tac >>
  Cases_on `lr` >> fs[return_def, AllCaseEqs()]
  >- (Cases_on `x` >> fs[return_def]
      >- gvs[] >>
      `runtime_consistent env cx st_after` by
        (qpat_x_assum `!a b c d. _` kall_tac >>
         fs[runtime_consistent_def] >>
         qpat_assum `eval_for _ _ _ _ [_] _ = _`
           (mp_then Any mp_tac (cj 4 eval_scc_type_sound_mutual)) >>
         disch_then (drule_all o SRULE []) >> simp[] >> fs[]) >>
      qpat_x_assum `!a b c d. _`
        (qspecl_then [`st`, `stp`, `stp`, `st_after`] mp_tac) >>
      asm_rewrite_tac[ignore_bind_def] >> strip_tac >>
      gvs[] >> first_x_assum drule_all >> simp[]) >>
  gvs[]
QED

Resume eval_storage_well_formed_on_mutual[Expr_Call_RawRevert]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Call _ _ _ _))` mp_tac >>
     pure_rewrite_tac[int_calls_expr_def] >> strip_tac) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Call _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (Call _ _ _ _)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ (Call _ _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, raise_def, return_def] >>
  Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (er,st1)` >>
  Cases_on `er` >> simp_tac(srw_ss())[bind_def, raise_def, return_def] >>
  rpt IF_CASES_TAC >> simp_tac(srw_ss())[bind_def, raise_def, return_def] >>
  strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[Expr_Call_RawLog]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Call _ _ _ _))` mp_tac >>
     pure_rewrite_tac[int_calls_expr_def] >> strip_tac) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Call _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  drule raw_log_well_typed_args >> strip_tac >>
  qpat_x_assum `eval_expr _ (Call _ _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, raise_def, return_def, push_log_def] >>
  Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (er,st1)` >>
  Cases_on `er` >> simp_tac(srw_ss())[bind_def, raise_def, return_def]
  >- (simp_tac(srw_ss())[lift_option_type_def, bind_def, ignore_bind_def,
        type_check_def, assert_def, raise_def, return_def, push_log_def] >>
      Cases_on `LENGTH x = 2` >> simp_tac(srw_ss())[]
      >- (Cases_on `dest_ArrayV (HD x)` >>
          simp_tac(srw_ss())[bind_def, return_def, raise_def]
          >- (strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]) >>
          Cases_on `dest_BytesV (EL 1 x)` >>
          simp_tac(srw_ss())[bind_def, return_def, raise_def]
          >- (strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]) >>
          simp_tac(srw_ss())[LET_THM, bind_def, ignore_bind_def,
            assert_def, return_def, raise_def, push_log_def] >>
          rpt IF_CASES_TAC >> simp_tac(srw_ss())[bind_def, return_def, raise_def] >>
          strip_tac >> gvs[] >> first_x_assum drule_all >>
          simp_tac(srw_ss())[] >> strip_tac >>
          irule (iffRL storage_well_formed_on_backends) >> qexists `st1` >> simp[]) >>
      strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]) >>
  strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[Expr_Call_SelfDestructTarget]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Call _ _ _ _))` mp_tac >>
     pure_rewrite_tac[int_calls_expr_def] >> strip_tac) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Call _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (Call _ _ _ _)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ (Call _ _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, raise_def, return_def] >>
  Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (er,st1)` >>
  Cases_on `er` >> simp_tac(srw_ss())[bind_def, raise_def, return_def]
  >- (simp_tac(srw_ss())[lift_option_type_def, bind_def, ignore_bind_def,
        get_accounts_def, return_def, raise_def, LET_THM] >>
      Cases_on `LENGTH x = 1` >> simp_tac(srw_ss())[]
      >- (Cases_on `dest_AddressV (HD x)` >>
          simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
            get_accounts_def, LET_THM]
          >- (strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]) >>
          qmatch_goalsub_abbrev_tac `transfer_value sender recipient amount st1` >>
          Cases_on `transfer_value sender recipient amount st1` >>
          rename1 `transfer_value sender recipient amount st1 = (tr,st2)` >>
          `?suffix. st2.storage_trace = st1.storage_trace ++ suffix` by
            (irule (INST_TYPE [alpha |-> ``:unit``] storage_trace_frame_prefix) >>
             qexistsl [`transfer_value sender recipient amount`, `tr`] >>
             simp_tac(srw_ss())[storage_trace_frame_transfer_value] >>
             first_assum ACCEPT_TAC) >>
          Cases_on `tr` >> simp_tac(srw_ss())[return_def] >>
          strip_tac >> gvs[] >>
          `storage_observations_ok cx H st1.storage_trace` by
            metis_tac[storage_observations_ok_prefix] >>
          `storage_well_formed_on cx st1 (FST H)` by
            (first_x_assum drule_all >> simp[]) >>
          drule_all transfer_value_preserves_storage_well_formed_on >> simp[]) >>
      strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]) >>
  strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[Expr_Call_RawCallCalldataTarget]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Call _ _ _ _))` mp_tac >>
     pure_rewrite_tac[int_calls_expr_def] >> strip_tac) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Call _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (Call _ _ _ _)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  (qpat_x_assum `eval_expr _ (Call _ _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, raise_def, return_def] >>
  Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (er,st1)` >>
  Cases_on `er` >> simp_tac(srw_ss())[bind_def, raise_def, return_def]
  >- (simp_tac(srw_ss())[lift_option_type_def, bind_def, ignore_bind_def,
        return_def, raise_def] >>
      Cases_on `LENGTH x = 1 + LENGTH flags.rcf_kws` >> simp_tac(srw_ss())[]
      >- (Cases_on `dest_AddressV (EL 0 x)` >>
          simp_tac(srw_ss())[bind_def, return_def, raise_def] >>
          simp_tac(srw_ss())[return_def, raise_def]
          >- (strip_tac >> gvs[raise_def, return_def] >> first_x_assum drule_all >> simp[]) >>
          Cases_on `raw_call_value flags.rcf_kws (DROP 1 x)` >>
          simp_tac(srw_ss())[bind_def, return_def, raise_def]
          >- (strip_tac >> gvs[return_def, raise_def] >> first_x_assum drule_all >> simp[]) >>
          strip_tac >> gvs[return_def] >>
          `?suffix. st'.storage_trace = st1.storage_trace ++ suffix` by
            (qpat_assum `eval_raw_call _ _ _ _ _ _ _ = _`
               (mp_then Any mp_tac storage_trace_frame_prefix) >>
             simp[storage_trace_frame_raw_call]) >>
          `storage_observations_ok cx H st1.storage_trace` by
            metis_tac[storage_observations_ok_prefix] >>
          `storage_well_formed_on cx st1 (FST H)` by
            (first_x_assum drule_all >> simp[]) >>
          drule_all eval_raw_call_preserves_storage_well_formed_on >> simp[]) >>
      strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]) >>
  strip_tac >> gvs[] >> first_x_assum (qspec_then `env` mp_tac) >>
  disch_then drule_all >> simp[])
QED

Resume eval_storage_well_formed_on_mutual[Expr_Call_RawCallTarget]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Call _ _ _ _))` mp_tac >>
     pure_rewrite_tac[int_calls_expr_def] >> strip_tac) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Call _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (Call _ _ _ _)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  (qpat_x_assum `eval_expr _ (Call _ _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, raise_def, return_def] >>
  Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (er,st1)` >>
  Cases_on `er` >> simp_tac(srw_ss())[bind_def, raise_def, return_def]
  >- (simp_tac(srw_ss())[lift_option_type_def, bind_def, ignore_bind_def,
        return_def, raise_def] >>
      Cases_on `LENGTH x = 2 + LENGTH flags.rcf_kws` >> simp_tac(srw_ss())[]
      >- (Cases_on `dest_AddressV (EL 0 x)` >>
          simp_tac(srw_ss())[bind_def, return_def, raise_def]
          >- (strip_tac >> gvs[raise_def, return_def] >> first_x_assum drule_all >> simp[]) >>
          Cases_on `dest_BytesV (EL 1 x)` >>
          simp_tac(srw_ss())[bind_def, return_def, raise_def]
          >- (strip_tac >> gvs[raise_def, return_def] >> first_x_assum drule_all >> simp[]) >>
          Cases_on `raw_call_value flags.rcf_kws (DROP 2 x)` >>
          simp_tac(srw_ss())[bind_def, return_def, raise_def]
          >- (strip_tac >> gvs[return_def, raise_def] >> first_x_assum drule_all >> simp[]) >>
          strip_tac >> gvs[return_def] >>
          `?suffix. st'.storage_trace = st1.storage_trace ++ suffix` by
            (qpat_assum `eval_raw_call _ _ _ _ _ _ _ = _`
               (mp_then Any mp_tac storage_trace_frame_prefix) >>
             simp[storage_trace_frame_raw_call]) >>
          `storage_observations_ok cx H st1.storage_trace` by
            metis_tac[storage_observations_ok_prefix] >>
          `storage_well_formed_on cx st1 (FST H)` by
            (first_x_assum drule_all >> simp[]) >>
          drule_all eval_raw_call_preserves_storage_well_formed_on >> simp[]) >>
      strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]) >>
  strip_tac >> gvs[] >> first_x_assum (qspec_then `env` mp_tac) >>
  disch_then drule_all >> simp[])
QED

Resume eval_storage_well_formed_on_mutual[Expr_Call_Send]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Call _ _ _ _))` mp_tac >>
     pure_rewrite_tac[int_calls_expr_def] >> strip_tac) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Call _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (Call _ _ _ _)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  `LENGTH es = if has_gas then 3 else 2` by
    (qpat_assum `MAP expr_type es = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     Cases_on `has_gas` >> simp[]) >>
  gvs[type_check_def, assert_def, return_def, raise_def] >>
  (qpat_x_assum `eval_expr _ (Call _ _ _ _) _ = _` mp_tac >>
   simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
     type_check_def, assert_def, return_def, raise_def] >>
   Cases_on `eval_exprs cx es st` >> rename1 `eval_exprs cx es st = (er,st1)` >>
   Cases_on `er` >> simp_tac(srw_ss())[bind_def, return_def, raise_def]
   >- (strip_tac >> gvs[] >>
       `?suffix. st'.storage_trace = st1.storage_trace ++ suffix` by
         (qpat_assum `eval_send _ _ _ _ = _`
            (mp_then Any mp_tac storage_trace_frame_prefix) >>
          simp[storage_trace_frame_send]) >>
       `storage_observations_ok cx H st1.storage_trace` by
         metis_tac[storage_observations_ok_prefix] >>
       `storage_well_formed_on cx st1 (FST H)` by
         (first_x_assum drule_all >> simp[]) >>
       drule_all eval_send_preserves_storage_well_formed_on >> simp[]) >>
   strip_tac >> gvs[] >> first_x_assum (qspec_then `env` mp_tac) >>
   disch_then drule_all >> simp[])
QED

Resume eval_storage_well_formed_on_mutual[Expr_Call_ExtCall]:
  rpt gen_tac >> strip_tac >> reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Call _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Call _ _ _ _))` mp_tac >>
     pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
     irule call_evaluation_safe_append_left >> goal_assum (drule_at Any)) >>
  `well_typed_exprs env es` by metis_tac[vyperTypeBuiltinsTheory.ext_call_args_typed] >>
  PairCases_on `sig` >>
  `well_typed_exprs env (TAKE 1 es) /\
   well_typed_exprs env (TAKE (LENGTH sig1) (DROP 1 es)) /\
   well_typed_exprs env (DROP (1 + LENGTH sig1) es)` by
    metis_tac[well_typed_exprs_TAKE, well_typed_exprs_DROP] >>
  `call_evaluation_safe cx (int_calls_exprs (TAKE 1 es)) /\
   call_evaluation_safe cx (int_calls_exprs (TAKE (LENGTH sig1) (DROP 1 es))) /\
   call_evaluation_safe cx (int_calls_exprs (DROP (1 + LENGTH sig1) es))` by
    metis_tac[call_evaluation_safe_exprs_TAKE, call_evaluation_safe_exprs_DROP] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_exprs cx (TAKE 1 es) st` >>
  rename1 `eval_exprs cx (TAKE 1 es) st = (target_res,target_st)` >>
  Cases_on `target_res` >> simp_tac(srw_ss())[bind_apply, LET_THM]
  >- (Cases_on `eval_expr_results cx (TAKE (LENGTH sig1) (DROP 1 es)) target_st` >>
      rename1 `eval_expr_results _ _ target_st = (capture_res,capture_st)` >>
      Cases_on `capture_res` >> simp_tac(srw_ss())[]
      >- (Cases_on `eval_exprs cx (DROP (1 + LENGTH sig1) es) capture_st` >>
          rename1 `eval_exprs _ _ capture_st = (kw_res,kw_st)` >>
          Cases_on `kw_res` >> simp_tac(srw_ss())[]
          >- (Cases_on `read_results cx x' kw_st` >>
              drule read_results_state >> disch_then SUBST_ALL_TAC >>
              simp_tac(srw_ss())[] >>
              Cases_on `q` >> simp_tac(srw_ss())[] >> strip_tac >>
              `storage_observations_ok cx H kw_st.storage_trace` by
                metis_tac[storage_trace_frame_prefix, storage_trace_frame_ext_call,
                          storage_observations_ok_prefix] >>
              `storage_observations_ok cx H capture_st.storage_trace` by
                metis_tac[storage_trace_frame_prefix, cj 6 evaluate_storage_trace_frame,
                          storage_observations_ok_prefix] >>
              `storage_observations_ok cx H target_st.storage_trace` by
                metis_tac[storage_trace_frame_prefix, cj 11 evaluate_storage_trace_frame,
                          storage_observations_ok_prefix] >>
              `storage_well_formed_on cx target_st (FST H)` by
                (qpat_x_assum `!env' st'' res st'''. well_typed_exprs _ (TAKE 1 es) /\ _ ==> _`
                   drule_all >> simp[]) >>
              `runtime_consistent env cx target_st` by
                metis_tac[eval_exprs_preserves_runtime_consistent] >>
              `storage_well_formed_on cx capture_st (FST H)` by
                (qpat_x_assum `!s target t nargs. eval_exprs _ _ _ = _ /\ _ ==> _`
                   (drule o SIMP_RULE (srw_ss()) []) >>
                 strip_tac >> first_x_assum drule_all >> simp[]) >>
              `runtime_consistent env cx capture_st` by
                (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
                 drule_all (cj 1 (SPEC_ALL (cj 11 eval_scc_type_sound_results_mutual))) >>
                 simp[vyperTypeExprSoundnessTheory.runtime_consistent_def]) >>
              `storage_well_formed_on cx kw_st (FST H)` by
                (qpat_x_assum `!s target t nargs s1 rs t1. _ ==> _`
                   (drule o SIMP_RULE (srw_ss()) []) >>
                 disch_then drule >> strip_tac >> first_x_assum drule_all >> simp[]) >>
              metis_tac[eval_ext_call_preserves_storage_well_formed_on]) >>
          strip_tac >> gvs[] >>
          `storage_observations_ok cx H capture_st.storage_trace` by
            metis_tac[storage_trace_frame_prefix, cj 6 evaluate_storage_trace_frame,
                      storage_observations_ok_prefix] >>
          `storage_observations_ok cx H target_st.storage_trace` by
            metis_tac[storage_trace_frame_prefix, cj 11 evaluate_storage_trace_frame,
                      storage_observations_ok_prefix] >>
          `storage_well_formed_on cx target_st (FST H)` by
            (qpat_x_assum `!env' st'' res st'''. well_typed_exprs _ (TAKE 1 es) /\ _ ==> _`
               drule_all >> simp[]) >>
          `runtime_consistent env cx target_st` by
            metis_tac[eval_exprs_preserves_runtime_consistent] >>
          `storage_well_formed_on cx capture_st (FST H)` by
            (qpat_x_assum `!s target t. _ ==> _`
               (drule o SIMP_RULE (srw_ss()) []) >>
             strip_tac >> first_x_assum drule_all >> simp[]) >>
          `runtime_consistent env cx capture_st` by
            (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
             drule_all (cj 1 (SPEC_ALL (cj 11 eval_scc_type_sound_results_mutual))) >>
             simp[vyperTypeExprSoundnessTheory.runtime_consistent_def]) >>
          qpat_x_assum `!s target t s1 rs t1. _ ==> _`
            (drule o SIMP_RULE (srw_ss()) []) >>
          disch_then drule >> strip_tac >> first_x_assum drule_all >> simp[]) >>
      strip_tac >> gvs[] >>
      `storage_observations_ok cx H target_st.storage_trace` by
        metis_tac[storage_trace_frame_prefix, cj 11 evaluate_storage_trace_frame,
                  storage_observations_ok_prefix] >>
      `storage_well_formed_on cx target_st (FST H)` by
        (qpat_x_assum `!env' st'' res st'''. well_typed_exprs _ (TAKE 1 es) /\ _ ==> _`
           drule_all >> simp[]) >>
      `runtime_consistent env cx target_st` by
        metis_tac[eval_exprs_preserves_runtime_consistent] >>
      qpat_x_assum `!s target t. _ ==> _`
        (drule o SIMP_RULE (srw_ss()) []) >>
      strip_tac >> first_x_assum drule_all >> simp[]) >>
  strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[Expr_Call_CreateTarget]:
  rpt gen_tac >> strip_tac >> reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Call _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (qpat_assum `call_evaluation_safe cx (int_calls_expr (Call _ _ _ _))` mp_tac >>
     pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
     irule call_evaluation_safe_append_left >> goal_assum (drule_at Any)) >>
  qpat_x_assum `well_typed_expr env (Call _ _ _ _)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  Cases_on `kind` >>
  rule_assum_tac (REWRITE_RULE [vyperASTTheory.create_kind_11, vyperASTTheory.create_kind_distinct]) >>
  rpt BasicProvers.VAR_EQ_TAC
  >~ [`RawCreate`] >- suspend "FiniteRawCreate"
  >~ [`CreateFromBlueprint raw_args`] >- suspend "FiniteBlueprint" >>
  full_simp_tac bool_ss [vyperASTTheory.create_kind_11, vyperASTTheory.create_kind_distinct] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (args_res,args_st)` >>
  Cases_on `args_res` >> simp_tac(srw_ss())[] >> strip_tac >> gvs[] >>
  `storage_observations_ok cx H args_st.storage_trace` by
    metis_tac[storage_trace_frame_prefix, storage_trace_frame_create,
              storage_observations_ok_prefix] >>
  first_x_assum drule_all >> strip_tac >>
  metis_tac[eval_create_preserves_storage_well_formed_on]
QED

Resume eval_storage_well_formed_on_mutual[FiniteBlueprint]:
  markerLib.RESUME_TAC >>
  full_simp_tac bool_ss [vyperASTTheory.create_kind_11, vyperASTTheory.create_kind_distinct] >>
  `well_typed_exprs env (TAKE (if has_salt then 4 else 3) es) /\
   well_typed_exprs env (DROP (if has_salt then 4 else 3) es)` by
    metis_tac[well_typed_exprs_TAKE, well_typed_exprs_DROP] >>
  `call_evaluation_safe cx (int_calls_exprs (TAKE (if has_salt then 4 else 3) es)) /\
   call_evaluation_safe cx (int_calls_exprs (DROP (if has_salt then 4 else 3) es))` by
    metis_tac[call_evaluation_safe_exprs_TAKE, call_evaluation_safe_exprs_DROP] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_exprs cx (TAKE (if has_salt then 4 else 3) es) st` >>
  rename1 `eval_exprs _ _ st = (prefix_res,prefix_st)` >>
  Cases_on `prefix_res` >> simp_tac(srw_ss())[bind_apply, LET_THM]
  >- (Cases_on `check_create_blueprint has_salt x prefix_st` >>
      rename1 `check_create_blueprint _ _ _ = (gate_res,gate_st)` >>
      `gate_st = prefix_st` by
        (qpat_assum `check_create_blueprint _ _ _ = _`
          (mp_tac o Q.AP_TERM `SND`) >> simp[]) >>
      qpat_x_assum `gate_st = prefix_st` SUBST_ALL_TAC >>
      Cases_on `gate_res` >> simp_tac(srw_ss())[bind_apply, LET_THM]
      >- (Cases_on `eval_expr_results cx (DROP (if has_salt then 4 else 3) es) prefix_st` >>
          rename1 `eval_expr_results _ _ _ = (suffix_res,suffix_st)` >>
          Cases_on `suffix_res` >> simp_tac(srw_ss())[bind_apply, LET_THM]
          >- (rename1 `eval_expr_results _ _ _ = (INL results,suffix_st)` >>
              Cases_on `read_results cx results suffix_st` >>
              drule read_results_state >> strip_tac >> gvs[] >>
              Cases_on `q` >> simp_tac(srw_ss())[] >> strip_tac >> gvs[] >>
              suspend "FiniteBlueprintSuffix") >>
          strip_tac >> gvs[] >> suspend "FiniteBlueprintCaptureError") >>
      strip_tac >> gvs[] >>
      first_x_assum drule_all >> simp[]) >>
  strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[FiniteBlueprintSuffix]:
  markerLib.RESUME_TAC >>
  rename1 `eval_expr_results _ _ prefix_st = (INL results,suffix_st)` >>
  `storage_observations_ok cx H suffix_st.storage_trace` by
    metis_tac[storage_trace_frame_prefix, storage_trace_frame_create,
              storage_observations_ok_prefix] >>
  `storage_observations_ok cx H prefix_st.storage_trace` by
    metis_tac[storage_trace_frame_prefix, cj 11 evaluate_storage_trace_frame,
              storage_observations_ok_prefix] >>
  `storage_well_formed_on cx prefix_st (FST H)` by
    (first_x_assum drule_all >> simp[]) >>
  `runtime_consistent env cx prefix_st` by
    metis_tac[eval_exprs_preserves_runtime_consistent] >>
  qpat_x_assum `!s prefix t s1 code_size t1. _ ==> _` drule_all >>
  strip_tac >>
  `storage_well_formed_on cx suffix_st (FST H)` by
    (first_x_assum drule_all >> simp[]) >>
  metis_tac[eval_create_preserves_storage_well_formed_on]
QED

Resume eval_storage_well_formed_on_mutual[FiniteBlueprintCaptureError]:
  markerLib.RESUME_TAC >>
  `storage_observations_ok cx H prefix_st.storage_trace` by
    metis_tac[storage_trace_frame_prefix, cj 11 evaluate_storage_trace_frame,
              storage_observations_ok_prefix] >>
  `storage_well_formed_on cx prefix_st (FST H)` by
    (first_x_assum drule_all >> simp[]) >>
  `runtime_consistent env cx prefix_st` by
    metis_tac[eval_exprs_preserves_runtime_consistent] >>
  qpat_x_assum `!s prefix t s1 code_size t1. _ ==> _` drule_all >>
  strip_tac >> first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[FiniteRawCreate]:
  markerLib.RESUME_TAC >>
  full_simp_tac bool_ss [vyperASTTheory.create_kind_11, vyperASTTheory.create_kind_distinct] >>
  `well_typed_exprs env (TAKE 2 es) /\
   well_typed_exprs env (TAKE (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es)) /\
   well_typed_exprs env (DROP (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es))` by
    metis_tac[well_typed_exprs_TAKE, well_typed_exprs_DROP] >>
  `call_evaluation_safe cx (int_calls_exprs (TAKE 2 es)) /\
   call_evaluation_safe cx (int_calls_exprs (TAKE (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es))) /\
   call_evaluation_safe cx (int_calls_exprs (DROP (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es)))` by
    metis_tac[call_evaluation_safe_exprs_TAKE, call_evaluation_safe_exprs_DROP] >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_exprs cx (TAKE 2 es) st` >>
  rename1 `eval_exprs _ _ st = (prefix_res,prefix_st)` >>
  Cases_on `prefix_res` >> simp_tac(srw_ss())[bind_apply, LET_THM, LENGTH_DROP]
  >- (Cases_on `eval_expr_results cx (TAKE (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es)) prefix_st` >>
      rename1 `eval_expr_results _ _ _ = (capture_res,capture_st)` >>
      Cases_on `capture_res` >> simp_tac(srw_ss())[bind_apply, LET_THM]
      >- (rename1 `eval_expr_results _ _ _ = (INL results,capture_st)` >>
          Cases_on `read_results cx results capture_st` >>
          drule read_results_state >> strip_tac >>
          rename1 `read_results _ _ _ = (read_res,read_st)` >>
          qpat_x_assum `read_st = capture_st` SUBST_ALL_TAC >>
          Cases_on `read_res` >> simp_tac(srw_ss())[bind_apply, LET_THM]
          >- (Cases_on `eval_exprs cx (DROP (LENGTH es - 2 - (if has_salt then 1 else 0)) (DROP 2 es)) capture_st` >>
              rename1 `eval_exprs _ _ capture_st = (salt_res,salt_st)` >>
              Cases_on `salt_res` >> simp_tac(srw_ss())[] >>
              strip_tac >> gvs[] >> suspend "FiniteRawSalt") >>
          strip_tac >> gvs[] >> suspend "FiniteRawCapture") >>
      strip_tac >> gvs[] >> suspend "FiniteRawCapture") >>
  strip_tac >> gvs[] >> first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[FiniteRawCapture]:
  markerLib.RESUME_TAC >>
  rename1 `eval_expr_results _ _ prefix_st = (_,capture_st)` >>
  `storage_observations_ok cx H prefix_st.storage_trace` by
    metis_tac[storage_trace_frame_prefix, cj 11 evaluate_storage_trace_frame,
              storage_observations_ok_prefix] >>
  `storage_well_formed_on cx prefix_st (FST H)` by
    (first_x_assum drule_all >> simp[]) >>
  `runtime_consistent env cx prefix_st` by
    metis_tac[eval_exprs_preserves_runtime_consistent] >>
  qpat_x_assum `!s prefix t. _ ==> _` drule_all >> strip_tac >>
  rule_assum_tac (REWRITE_RULE [LENGTH_DROP]) >>
  first_x_assum drule_all >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[FiniteRawSalt]:
  markerLib.RESUME_TAC >>
  rename1 `eval_expr_results _ _ prefix_st = (INL results,capture_st)` >>
  rename1 `eval_exprs _ (DROP _ (DROP 2 es)) capture_st = (_,salt_st)` >>
  `storage_observations_ok cx H salt_st.storage_trace` by
    metis_tac[storage_trace_frame_prefix, storage_trace_frame_create,
              storage_observations_ok_prefix] >>
  `storage_observations_ok cx H capture_st.storage_trace` by
    metis_tac[storage_trace_frame_prefix, cj 6 evaluate_storage_trace_frame,
              storage_observations_ok_prefix] >>
  `storage_observations_ok cx H prefix_st.storage_trace` by
    metis_tac[storage_trace_frame_prefix, cj 11 evaluate_storage_trace_frame,
              storage_observations_ok_prefix] >>
  `storage_well_formed_on cx prefix_st (FST H)` by
    (first_x_assum drule_all >> simp[]) >>
  `runtime_consistent env cx prefix_st` by
    metis_tac[eval_exprs_preserves_runtime_consistent] >>
  `storage_well_formed_on cx capture_st (FST H)` by
    (qpat_x_assum `!s prefix t. _ ==> _` drule_all >>
     strip_tac >> first_x_assum drule_all >> simp[]) >>
  `runtime_consistent env cx capture_st` by
    (fs[vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
     drule_all (cj 1 (SPEC_ALL (cj 11 eval_scc_type_sound_results_mutual))) >>
     simp[vyperTypeExprSoundnessTheory.runtime_consistent_def]) >>
  qpat_x_assum `!s prefix t s1 results t1 s2 args t2. _ ==> _` drule_all >>
  strip_tac >>
  `storage_well_formed_on cx salt_st (FST H)` by
    (first_x_assum drule_all >> simp[]) >>
  metis_tac[eval_create_preserves_storage_well_formed_on]
QED

Resume eval_storage_well_formed_on_mutual[Expr_Call_IntCall]:
  rpt gen_tac >> strip_tac >> reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Call _ (IntCall _) _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (irule call_evaluation_safe_mono >>
     goal_assum (drule_at Any) >> simp[int_calls_expr_def]) >>
  qpat_x_assum `well_typed_expr env (Call _ (IntCall _) _ _)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac[Once evaluate_def] >>
  simp_tac(srw_ss())[bind_apply, ignore_bind_apply, LET_THM] >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac vyperStatePreservationTheory.type_check_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC
  >- (strip_tac >> rpt (qpat_x_assum `!x. _` kall_tac) >>
      gvs[type_check_def, assert_def]) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac vyperStatePreservationTheory.lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC
  >- (strip_tac >> rpt (qpat_x_assum `!x. _` kall_tac) >> gvs[]) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac vyperStatePreservationTheory.lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC
  >- (strip_tac >> rpt (qpat_x_assum `!x. _` kall_tac) >> gvs[]) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac vyperStatePreservationTheory.type_check_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC
  >- (strip_tac >> rpt (qpat_x_assum `!x. _` kall_tac) >> gvs[]) >>
  simp_tac(srw_ss())[bind_apply] >>
  BasicProvers.TOP_CASE_TAC >>
  qmatch_asmsub_rename_tac `eval_expr_results cx es st = (args_res,args_st)` >>
  qpat_assum `type_check _ "IntCall args length" _ = _`
    (strip_assume_tac o SRULE [type_check_def, assert_def, return_def,
                              raise_def, AllCaseEqs()]) >>
  BasicProvers.VAR_EQ_TAC >>
  first_x_assum (drule_at (Pat `type_check _ "recursion" _ = _`)) >>
  disch_then (drule_at (Pat `lift_option_type (get_module_code _ _) _ _ = _`)) >>
  disch_then (drule_at (Pat `lift_option_type (lookup_callable_function _ _ _) _ _ = _`)) >>
  simp_tac(srw_ss())[] >>
  disch_then (assume_tac o SRULE
    [type_check_def, assert_def, return_def, raise_def]) >>
  ntac 2
    (first_x_assum (drule_at (Pat `type_check _ "recursion" _ = _`)) >>
     disch_then (drule_at (Pat `lift_option_type (get_module_code _ _) _ _ = _`)) >>
     disch_then (drule_at (Pat `lift_option_type (lookup_callable_function _ _ _) _ _ = _`)) >>
     disch_then (assume_tac o SRULE
       [type_check_def, assert_def, return_def, raise_def, get_scopes_def,
        set_scopes_def, push_function_def])) >>
  qpat_assum `runtime_consistent env cx _`
    (strip_assume_tac o SRULE [runtime_consistent_def]) >>
  drule_all (cj 1 (cj 11 eval_scc_type_sound_results_mutual)) >> strip_tac >>
  Cases_on `args_res`
  >- (ntac 2
        (first_x_assum (drule_at (Pat `eval_expr_results _ _ _ = _`)) >>
         disch_then (assume_tac o SRULE [])) >>
      qpat_assum `lift_option_type (get_module_code cx _) _ _ = _`
        (strip_assume_tac o SRULE [lift_option_type_def, vyperMiscTheory.option_CASE_rator, return_def, raise_def, AllCaseEqs()]) >>
      qpat_assum `lift_option_type (lookup_callable_function _ _ _) _ _ = _`
        (strip_assume_tac o SRULE [lift_option_type_def, vyperMiscTheory.option_CASE_rator, return_def, raise_def, AllCaseEqs()]) >>
      qmatch_asmsub_rename_tac `lookup_callable_function _ _ _ = SOME callable` >>
      PairCases_on `callable` >>
      `IS_SOME (FLOOKUP env.fn_sigs (src_id_opt,fn))` by simp[] >>
      drule_all callable_body_typing_from_env_consistent >>
      disch_then (CONJUNCTS_THEN2 assume_tac
        (qx_choose_then `env_body` (qx_choose_then `ret_tv`
          (qx_choose_then `env_after` (fn th => map_every assume_tac (CONJUNCTS th)))))) >>
      drule_all intcall_default_env_side_conditions >>
      disch_then (qspec_then `fn` strip_assume_tac) >>
      `runtime_consistent (defaults_env env_body)
         (cx with stk updated_by CONS (src_id_opt,fn))
         (args_st with scopes := [FEMPTY])` by
        (simp[runtime_consistent_def] >> conj_tac
         >- (irule defaults_env_empty_frame_consistent >> simp[]) >>
         fs[vyperTypeInvariantsTheory.state_well_typed_def,
            vyperTypeInvariantsTheory.scope_well_typed_def]) >>
      `call_evaluation_safe (cx with stk updated_by CONS (src_id_opt,fn))
        (int_calls_exprs (DROP (LENGTH callable3 - (LENGTH callable2 - LENGTH es)) callable3))` by
        (qpat_assum `get_module_code _ _ = SOME _` mp_tac >>
         qpat_assum `lookup_callable_function _ _ _ = SOME _` mp_tac >>
         qpat_assum `call_evaluation_safe cx (int_calls_expr (Call _ _ _ _))` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >>
         simp[int_calls_expr_def] >> rpt strip_tac >>
         irule call_evaluation_safe_push_needed_defaults >> metis_tac[]) >>
      `well_typed_exprs (defaults_env env_body)
        (DROP (LENGTH callable3 - (LENGTH callable2 - LENGTH es)) callable3)` by
        (irule well_typed_exprs_DROP >> simp[]) >>
      simp_tac(srw_ss())[get_scopes_def, return_def] >>
      BasicProvers.TOP_CASE_TAC >>
      qmatch_asmsub_rename_tac `finally _ _ args_st = (defaults_res,defaults_st)` >>
      `storage_observations_ok cx H defaults_st.storage_trace ==>
       storage_well_formed_on cx defaults_st (FST H)` by
        suspend "IntCall_shared_defaults" >>
      reverse BasicProvers.TOP_CASE_TAC
      >- suspend "IntCall_probe_defaults_error" >>
      first_x_assum (drule_at (Pat `finally _ _ _ = _`)) >>
      disch_then (assume_tac o SRULE []) >>
      BasicProvers.TOP_CASE_TAC >>
      reverse BasicProvers.TOP_CASE_TAC
      >- suspend "IntCall_probe_read_error" >>
      first_x_assum (drule_at (Pat `read_results _ _ _ = _`)) >>
      disch_then (assume_tac o SRULE []) >>
      BasicProvers.TOP_CASE_TAC >>
      reverse BasicProvers.TOP_CASE_TAC
      >- suspend "IntCall_probe_bind_error" >>
      first_x_assum (drule_at (Pat `lift_option_type _ "IntCall bind_arguments" _ = _`)) >>
      disch_then (assume_tac o SRULE []) >>
      BasicProvers.TOP_CASE_TAC >>
      reverse BasicProvers.TOP_CASE_TAC
      >- suspend "IntCall_probe_ret_error" >>
      qpat_assum `evaluate_type (get_tenv cx) callable4 = SOME _`
        (fn eq => first_x_assum
          (drule_at (Pat `lift_option_type _ "IntCall eval ret" _ = _`) o
           PURE_REWRITE_RULE [eq])) >>
      disch_then (assume_tac o SRULE []) >>
      BasicProvers.TOP_CASE_TAC >>
      reverse BasicProvers.TOP_CASE_TAC
      >- suspend "IntCall_probe_lock_error" >>
      qmatch_asmsub_rename_tac `(if _ then _ else return ()) _ = (INL lock_unit,_)` >>
      Cases_on `lock_unit` >>
      first_x_assum (drule_at (Pat `(if _ then _ else return ()) _ = _`)) >>
      disch_then (assume_tac o SRULE []) >>
      simp_tac(srw_ss())[push_function_def, return_def] >>
      suspend "IntCall_body_integration") >>
  simp_tac(srw_ss())[] >> strip_tac >>
  first_x_assum (drule_at (Pat `eval_expr_results _ _ _ = _`)) >>
  disch_then (qspec_then `env` assume_tac) >>
  rpt (qpat_x_assum `!x. _` kall_tac) >> gvs[]
QED

Resume eval_storage_well_formed_on_mutual[IntCall_shared_defaults]:
  strip_tac >>
  qpat_x_assum `!s1 s2 d t s3. _` kall_tac >>
  `storage_observations_ok (cx with stk updated_by CONS (src_id_opt,fn))
     H defaults_st.storage_trace` by fs[storage_observations_ok_stk] >>
  `storage_well_formed_on (cx with stk updated_by CONS (src_id_opt,fn)) defaults_st (FST H)` by
    (irule default_finally_preserves_storage_well_formed_on >>
     qpat_assum `finally _ _ args_st = _` (irule_at Any) >>
     simp_tac(srw_ss())[] >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     map_every qx_gen_tac [`r`,`framed`] >> strip_tac >>
     `storage_observations_ok cx H args_st.storage_trace` by
       (qpat_assum `eval_exprs _ _ _ = _` mp_tac >>
        qpat_assum `storage_observations_ok (_ with stk updated_by _) H framed.storage_trace` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
        `storage_trace_frame (eval_exprs
           (cx with stk updated_by CONS (src_id_opt,fn))
           (DROP (LENGTH callable3 - (LENGTH callable2 - LENGTH es)) callable3))` by
          simp[cj 6 evaluate_storage_trace_frame] >>
        drule_all storage_trace_frame_prefix >> simp[] >> strip_tac >>
        gvs[storage_observations_ok_append, storage_observations_ok_stk]) >>
     `storage_well_formed_on cx args_st (FST H)` by
       (qpat_x_assum `!env st res st'. _ /\ well_typed_exprs env es /\ _ ==> _`
          (drule_at (Pat `eval_expr_results _ _ _ = _`)) >>
        disch_then (qspec_then `env` mp_tac) >> simp[]) >>
     qpat_x_assum `!env st res st'. _ /\ well_typed_exprs env (DROP _ _) /\ _ ==> _`
       (drule_at (Pat `eval_exprs _ _ _ = _`)) >>
     disch_then (qspec_then `defaults_env env_body` mp_tac) >>
     simp[storage_well_formed_on_scopes, storage_well_formed_on_stk]) >>
  qpat_x_assum `storage_well_formed_on (_ with stk updated_by _) defaults_st _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp[storage_well_formed_on_stk]
QED

Resume eval_storage_well_formed_on_mutual[IntCall_probe_defaults_error]:
  simp_tac(srw_ss())[] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `storage_observations_ok _ _ _ ==> storage_well_formed_on _ _ _` mp_tac >>
  qpat_x_assum `storage_observations_ok cx H _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[IntCall_probe_read_error]:
  simp_tac(srw_ss())[] >> strip_tac >>
  drule read_results_state >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `defaults_st = st'` SUBST_ALL_TAC >>
  qpat_x_assum `storage_observations_ok _ _ _ ==> storage_well_formed_on _ _ _` mp_tac >>
  qpat_x_assum `storage_observations_ok cx H _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[IntCall_probe_bind_error]:
  simp_tac(srw_ss())[] >> strip_tac >>
  drule read_results_state >> disch_then SUBST_ALL_TAC >>
  qpat_assum `lift_option_type _ "IntCall bind_arguments" _ = _`
    (mp_tac o MATCH_MP vyperStatePreservationTheory.lift_option_type_state) >>
  disch_then SUBST_ALL_TAC >> BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `storage_observations_ok _ _ _ ==> storage_well_formed_on _ _ _` mp_tac >>
  qpat_x_assum `storage_observations_ok cx H _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp[]
QED

Resume eval_storage_well_formed_on_mutual[IntCall_probe_ret_error]:
  qpat_assum `evaluate_type (get_tenv cx) callable4 = SOME _` mp_tac >>
  qpat_assum `lift_option_type _ "IntCall eval ret" _ = _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[lift_option_type_def, return_def]
QED

Resume eval_storage_well_formed_on_mutual[IntCall_body_integration]:
  qpat_x_assum `!env st res st'. _ /\ well_typed_exprs env es /\ _ ==> _` kall_tac >>
  qpat_x_assum `!env st res st'. _ /\ well_typed_exprs env (DROP _ _) /\ _ ==> _` kall_tac >>
  drule read_results_state >> disch_then SUBST_ALL_TAC >>
  qpat_assum `lift_option_type _ "IntCall bind_arguments" _ = _`
    (mp_tac o MATCH_MP vyperStatePreservationTheory.lift_option_type_state) >>
  disch_then SUBST_ALL_TAC >>
  qpat_assum `lift_option_type _ "IntCall eval ret" _ = _`
    (mp_tac o MATCH_MP vyperStatePreservationTheory.lift_option_type_state) >>
  disch_then SUBST_ALL_TAC >>
  qmatch_asmsub_rename_tac `(if _ then _ else return ()) defaults_st = (INL (),lock_st)` >>
  qmatch_goalsub_rename_tac `lock_st with scopes := [call_env]` >>
  drule default_finally_result >> strip_tac >>
  qpat_assum `runtime_consistent (defaults_env env_body) _ _`
    (strip_assume_tac o SRULE [runtime_consistent_def]) >>
  drule_at (Pat `eval_exprs _ _ _ = _`) (cj 1 (cj 6 eval_scc_type_sound_results_mutual)) >>
  disch_then (qspec_then `defaults_env env_body` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all default_restore_runtime_projections >> strip_tac >>
  qpat_assum `case INL _ of INL results => expr_results_typed _ _ _ | INR _ => _`
    (assume_tac o SRULE []) >>
  qpat_assum `case INL _ of INL vs => exprs_runtime_typed _ _ _ | INR _ => _`
    (assume_tac o SRULE []) >>
  drule_all read_results_restored_runtime_typed >> strip_tac >>
  `env.type_defs = get_tenv cx /\ fn_sigs_consistent env.fn_sigs cx` by
    (qpat_assum `env_consistent env cx args_st` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  `sig.param_types = MAP SND callable2 /\ sig.num_defaults = LENGTH callable3` by
    (qpat_assum `fn_sigs_consistent env.fn_sigs cx` mp_tac >>
     qpat_assum `FLOOKUP env.fn_sigs _ = SOME sig` mp_tac >>
     qpat_assum `get_module_code cx _ = SOME _` mp_tac >>
     qpat_assum `lookup_callable_function _ _ _ = SOME _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[vyperTypeInvariantsTheory.fn_sigs_consistent_def] >>
     rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[]) >>
  `MAP expr_type es = TAKE (LENGTH es) (MAP SND callable2)` by metis_tac[] >>
  `LENGTH callable2 - LENGTH es <= LENGTH callable3` by decide_tac >>
  drule_at (Pos hd) vyperTypeBindArgumentsTheory.intcall_bind_arguments_from_runtime_typed >>
  disch_then (drule_at (Pat `exprs_runtime_typed (defaults_env _) _ _`)) >>
  disch_then (drule_at (Pat `MAP expr_type _ = MAP SND _`)) >>
  disch_then (qspecl_then [`cx with stk updated_by CONS (src_id_opt,fn)`, `defaults_st`] mp_tac) >>
  (impl_tac >- (simp[vyperContextTheory.get_tenv_def] >> metis_tac[])) >> strip_tac >>
  `call_env' = call_env` by
    (qpat_assum `bind_arguments _ _ _ = SOME call_env'` mp_tac >>
     qpat_assum `lift_option_type _ "IntCall bind_arguments" _ = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[vyperContextTheory.get_tenv_def, lift_option_type_def, vyperStateTheory.return_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[vyperStateTheory.return_def]) >>
  qpat_x_assum `call_env' = call_env` SUBST_ALL_TAC >>
  drule_at (Pat `(if _ then _ else _) _ = _`) intcall_live_pushed_body_preconditions >>
  disch_then (qspecl_then [`env`, `env_body`] mp_tac) >>
  disch_then (qspecl_then [`args_st`, `call_env`, `fn`] mp_tac) >>
  (impl_tac >- (qpat_x_assum `defaults_st = _ with scopes := _` kall_tac >> simp[])) >>
  strip_tac >>
  `runtime_consistent env_body (cx with stk updated_by CONS (src_id_opt,fn))
     (lock_st with scopes := [call_env])` by
    (qpat_x_assum `defaults_st = _ with scopes := _` kall_tac >>
     simp[runtime_consistent_def] >> metis_tac[]) >>
  suspend "IntCall_finite_body_cleanup"
QED

Resume eval_storage_well_formed_on_mutual[IntCall_probe_lock_error]:
  rpt (qpat_x_assum `!x. _` kall_tac) >>
  drule read_results_state >> disch_then SUBST_ALL_TAC >>
  qpat_assum `lift_option_type _ "IntCall bind_arguments" _ = _`
    (mp_tac o MATCH_MP vyperStatePreservationTheory.lift_option_type_state) >>
  disch_then SUBST_ALL_TAC >>
  qpat_assum `lift_option_type _ "IntCall eval ret" _ = _`
    (mp_tac o MATCH_MP vyperStatePreservationTheory.lift_option_type_state) >>
  disch_then SUBST_ALL_TAC >>
  rpt strip_tac >>
  qpat_x_assum `_ = st'` SUBST_ALL_TAC >>
  qpat_x_assum `storage_observations_ok cx H st'.storage_trace` mp_tac >>
  qpat_x_assum `storage_observations_ok cx H defaults_st.storage_trace ==> _` mp_tac >>
  qpat_x_assum `(if _ then _ else _) defaults_st = _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  Cases_on `callable1` >> simp_tac(srw_ss())[vyperStateTheory.return_def] >>
  Cases_on `cx.nonreentrant_slot` >>
  simp_tac(srw_ss())[vyperStateTheory.raise_def] >>
  simp_tac(srw_ss())[acquire_nonreentrant_lock_eq] >>
  IF_CASES_TAC
  >- (simp_tac(srw_ss())[] >> rpt strip_tac >>
      gvs[storage_observations_ok_append, storage_well_formed_on_def]) >>
  IF_CASES_TAC >> simp_tac(srw_ss())[]
QED

Resume eval_storage_well_formed_on_mutual[IntCall_finite_body_cleanup]:
  `call_evaluation_safe (cx with stk updated_by CONS (src_id_opt,fn))
     (int_calls_stmts callable5)` by
    (qpat_assum `get_module_code _ _ = SOME _` mp_tac >>
     qpat_assum `lookup_callable_function _ _ _ = SOME _` mp_tac >>
     qpat_assum `call_evaluation_safe cx (int_calls_expr (Call _ _ _ _))` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[int_calls_expr_def] >> rpt strip_tac >>
     irule call_evaluation_safe_push_body >> metis_tac[]) >>
  qpat_x_assum `runtime_consistent env_body _ (lock_st with scopes := _)` mp_tac >>
  qpat_x_assum `call_evaluation_safe _ (int_calls_stmts callable5)` mp_tac >>
  qpat_x_assum `functions_well_typed (cx with stk updated_by _)` mp_tac >>
  qpat_x_assum `!env' ret_ty env'' st res st'. _` mp_tac >>
  qpat_x_assum `type_stmts env_body _ _ = _` mp_tac >>
  qpat_x_assum `regions_consistent (FST H)` mp_tac >>
  qpat_x_assum `storage_locks_separated (FST H) (SND H)` mp_tac >>
  qpat_x_assum `storage_observations_ok cx H st'.storage_trace` mp_tac >>
  qpat_x_assum `storage_observations_ok cx H defaults_st.storage_trace ==> _` mp_tac >>
  qpat_x_assum `(if _ then _ else _) defaults_st = (INL (),lock_st)` mp_tac >>
  qpat_x_assum `LENGTH es <= LENGTH callable2` mp_tac >>
  qpat_x_assum `LENGTH callable2 <= LENGTH es + LENGTH callable3` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> ntac 12 disch_tac >>
  BasicProvers.TOP_CASE_TAC >>
  rename1 `finally _ _ _ = (final_res,final_st)` >>
  disch_tac >>
  `st' = final_st` by
    (qpat_x_assum `(case final_res of _ => _ | _ => _) = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `final_res` >>
     simp_tac(srw_ss())[] >> strip_tac
     >- (qpat_x_assum `(case lift_option_type _ _ _ of _ => _ | _ => _) = _` mp_tac >>
         BasicProvers.TOP_CASE_TAC >>
         drule vyperStatePreservationTheory.lift_option_type_state >>
         disch_then SUBST_ALL_TAC >> Cases_on `q` >> simp_tac(srw_ss())[] >>
         rpt strip_tac >> gvs[]) >> gvs[]) >>
  qpat_x_assum `st' = final_st` SUBST_ALL_TAC >>
  suspend "IntCall_finally_finite"
QED

Resume eval_storage_well_formed_on_mutual[IntCall_finally_finite]:
  qpat_x_assum `(case final_res of _ => _ | _ => _) = _` kall_tac >>
  qmatch_asmsub_abbrev_tac `finally handled cleanup body_input = _` >>
  Cases_on `handled body_input` >> rename1 `handled body_input = (hr,hs)` >>
  Cases_on `cleanup hs` >> rename1 `cleanup hs = (cr,cs)` >>
  `final_st = cs` by
    (qpat_x_assum `finally _ _ _ = _` mp_tac >>
     qpat_assum `handled body_input = _` mp_tac >>
     qpat_assum `cleanup hs = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
     Cases_on `hr` >> Cases_on `cr` >>
     gvs[finally_def, ignore_bind_def, bind_def, return_def, raise_def]) >>
  qpat_x_assum `final_st = cs` SUBST_ALL_TAC >>
  `storage_trace_frame cleanup` by
    (simp[Abbr `cleanup`] >> irule storage_trace_frame_ignore_bind >>
     simp[pop_function_def, storage_trace_frame_state_updates] >>
     Cases_on `callable1 /\ callable0 <> View /\ callable0 <> Pure` >>
     simp[storage_trace_frame_return] >> Cases_on `cx.nonreentrant_slot` >>
     simp[storage_trace_frame_return, storage_trace_frame_release_lock]) >>
  `storage_observations_ok cx H hs.storage_trace` by
    metis_tac[storage_trace_frame_prefix, storage_observations_ok_prefix] >>
  `storage_well_formed_on cx hs (FST H)` by
    suspend "IntCall_handled_finite" >>
  qpat_x_assum `cleanup hs = _` mp_tac >>
  simp[Abbr `cleanup`] >> strip_tac >>
  irule intcall_cleanup_preserves_storage_well_formed_on >>
  simp[] >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`callable0 = View \/ callable0 = Pure`, `callable1`, `args_st.scopes`, `cr`] >>
  simp[]
QED

Resume eval_storage_well_formed_on_mutual[IntCall_handled_finite]:
  Cases_on `eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) callable5 body_input` >>
  rename1 `eval_stmts _ _ body_input = (br,bs)` >>
  `hs = bs` by
    (qpat_x_assum `handled body_input = _` mp_tac >>
     simp_tac(srw_ss())[Abbr `handled`, try_def, ignore_bind_def, bind_def] >>
     qpat_assum `eval_stmts _ _ _ = _` (fn th => rewrite_tac[th]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `br`
     >- (simp_tac(srw_ss())[return_def] >> rpt strip_tac >> gvs[]) >>
     simp_tac(srw_ss())[] >>
     disch_then (mp_tac o MATCH_MP vyperEvalPreservesScopesTheory.handle_function_state) >> simp[]) >>
  qpat_x_assum `hs = bs` SUBST_ALL_TAC >>
  `storage_observations_ok (cx with stk updated_by CONS (src_id_opt,fn))
     H bs.storage_trace` by fs[storage_observations_ok_stk] >>
  `storage_observations_ok cx H body_input.storage_trace` by
    (drule_all eval_stmts_storage_observations_ok_input >>
     simp[storage_observations_ok_stk]) >>
  `storage_well_formed_on (cx with stk updated_by CONS (src_id_opt,fn)) body_input (FST H)` by
    suspend "IntCall_lock_success" >>
  first_x_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >>
  disch_then (qspecl_then [`env_body`,`callable4`,`env_after`] mp_tac) >>
  simp[storage_well_formed_on_stk]
QED

Resume eval_storage_well_formed_on_mutual[IntCall_lock_success]:
  qpat_x_assum `storage_observations_ok cx H body_input.storage_trace` mp_tac >>
  qpat_x_assum `storage_observations_ok cx H defaults_st.storage_trace ==> _` mp_tac >>
  qpat_x_assum `(if _ then _ else _) defaults_st = (INL (),lock_st)` mp_tac >>
  qpat_x_assum `regions_consistent (FST H)` mp_tac >>
  qpat_x_assum `storage_locks_separated (FST H) (SND H)` mp_tac >>
  simp_tac(srw_ss())[Abbr `body_input`, storage_well_formed_on_stk] >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
  `storage_well_formed_on cx lock_st (FST H)` suffices_by
    (simp[storage_well_formed_on_def] >> rpt strip_tac >>
     first_x_assum drule >> Cases_on `b` >> simp[get_storage_def]) >>
  qpat_x_assum `(if _ then _ else _) defaults_st = _` mp_tac >>
  Cases_on `callable1`
  >- (Cases_on `cx.nonreentrant_slot`
      >- simp_tac(srw_ss())[raise_def] >>
      simp_tac(srw_ss())[] >> strip_tac >>
      `storage_observations_ok cx H defaults_st.storage_trace` by
        metis_tac[storage_trace_frame_prefix, storage_trace_frame_acquire_lock,
                  storage_observations_ok_prefix] >>
      `MEM (StorageLock x) lock_st.storage_trace` by
        (qpat_x_assum `acquire_nonreentrant_lock _ _ _ _ = _` mp_tac >>
         simp[acquire_nonreentrant_lock_eq] >>
         rpt IF_CASES_TAC >> rpt strip_tac >> gvs[]) >>
      irule acquire_lock_preserves_storage_well_formed_on >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  simp_tac(srw_ss())[return_def] >> rpt strip_tac >> gvs[]
QED

Finalise eval_storage_well_formed_on_mutual
