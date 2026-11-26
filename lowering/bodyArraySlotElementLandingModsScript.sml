(* Land a reached array element at its current storage slot. *)
Theory bodyArraySlotElementLandingMods
Ancestors
  bodyFullPostsMods exprSimMemDefs loweringPosts accountsRelProps
  targetPlaceLive exprSimPopNestedBase stmtSimAssignStorageCopy
  vyperStorageBackend vyperStoragePlaceObserved vyperStoragePlaceRegion
  vyperStorageWritePreservation vyperLookupStorage vyperValue vyperState
  vyperAST vyperInterpreter context words

Theorem array_slot_element_observed[local]:
  storage_place_observed H (StoragePlace tr slot (ArrayTV etv bd)) /\
  0 <= i /\ Num i < bound_length bd /\
  off = (case bd of Fixed _ => 0 | Dynamic _ => 1) + Num i * type_slot_size etv ==>
  storage_place_observed H (StoragePlace tr (slot + n2w off) etv)
Proof
  strip_tac >>
  `storage_subregion (ArrayTV etv bd) [ValueSubscript (IntV i)] off etv` by
    (Cases_on `bd` >> gvs[bound_length_def, storage_subregion_def]) >>
  qpat_x_assum `off = _` kall_tac >>
  qpat_x_assum `storage_place_observed _ _` mp_tac >>
  rewrite_tac[storage_place_observed_def] >> strip_tac >>
  rename1 `storage_subregion rt path delta (ArrayTV etv bd)` >>
  rename1 `slot = root + n2w delta` >>
  qexistsl [`root`,`rt`,`path ++ [ValueSubscript (IntV i)]`,`delta + off`] >>
  simp[GSYM word_add_n2w, WORD_ADD_ASSOC] >>
  metis_tac[storage_subregion_append]
QED

Theorem array_slot_element_region[local]:
  storage_read_live H tr st slot (ArrayTV etv bd) /\
  slots_in_range st (w2n slot) (ArrayTV etv bd) /\
  w2n slot + type_slot_size (ArrayTV etv bd) <= dimword (:256) /\
  Num i < bound_length bd /\
  (!n. bd = Dynamic n ==> Num i < w2n (lookup_storage slot st)) /\
  off = (case bd of Fixed _ => 0 | Dynamic _ => 1) + Num i * type_slot_size etv ==>
  storage_read_live H tr st (slot + n2w off) etv /\
  slots_in_range st (w2n (slot + n2w off)) etv /\
  w2n (slot + n2w off) + type_slot_size etv <= dimword (:256)
Proof
  Cases_on `bd` >> simp[bound_length_def] >> strip_tac >> gvs[]
  >- (conj_tac >- metis_tac[nested_pop_live_fixed_element] >>
      conj_tac >- metis_tac[nested_pop_fixed_slots] >>
      once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
      irule (cj 4 fixed_array_child_region_bounds) >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- metis_tac[nested_pop_live_dynamic_element, arithmeticTheory.ADD_COMM] >>
  conj_tac >- metis_tac[nested_pop_dynamic_slots, arithmeticTheory.ADD_COMM] >>
  Cases_on `type_slot_size etv = 0`
  >- (simp[] >> qspec_then `(slot:bytes32) + 1w` mp_tac w2n_lt >> simp[]) >>
  `w2n (slot + n2w (1 + Num i * type_slot_size etv)) + type_slot_size etv <= dimword (:256)` by
    (irule (cj 4 dynamic_array_child_region_bounds) >>
     conj_tac >- simp[] >> qexists `n` >> simp[]) >>
  qpat_x_assum `w2n _ + _ <= _` mp_tac >>
  simp_tac (srw_ss()) [arithmeticTheory.ADD_COMM]
QED

Theorem array_slot_element_holds[local]:
  evaluate_type (get_tenv cx) et = SOME etv /\ well_formed_type_value etv /\
  stmt_state_rel (H : (bool # bytes32 # type_value) list # num list) ctx func cenv cx fin q /\
  storage_read_live H tr (get_storage cx fin tr) w etv /\
  slots_in_range (get_storage cx fin tr) (w2n w) etv /\
  w2n w + type_slot_size etv <= dimword (:256) ==>
  storage_holds cx tr et (PlaceR (StoragePlace tr w etv)) w fin q
Proof
  strip_tac >>
  drule storage_copy_initial_agree >>
  disch_then (qspec_then `tr` assume_tac) >>
  drule_all storage_range_agree_of_live >> strip_tac >>
  drule_all decode_value_from_slots_in_range >> strip_tac >>
  simp[storage_holds_def, read_storage_slot_eq, read_result_def,
       read_place_def, bind_def, return_def] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem array_slot_element_landing_mods:
  let off = (case bd of Fixed _ => 0 | Dynamic _ => 1) + Num i * type_slot_size etv;
      w = slot + n2w off;
      tv = PlaceR (StoragePlace tr w etv);
      vv = LocatedValue et (mk_ptr dst (slot_loc tr));
      e = Subscript et obj idx
  in
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  well_formed_type_value (ArrayTV etv bd) /\ well_formed_type_value etv /\
  storage_place_observed H (StoragePlace tr slot (ArrayTV etv bd)) /\
  storage_read_live H tr (get_storage cx fin tr) slot (ArrayTV etv bd) /\
  slots_in_range (get_storage cx fin tr) (w2n slot) (ArrayTV etv bd) /\
  w2n slot + type_slot_size (ArrayTV etv bd) <= dimword (:256) /\
  0 <= i /\ Num i < bound_length bd /\
  (!n. bd = Dynamic n ==> Num i < w2n (lookup_storage slot (get_storage cx fin tr))) /\
  eval_operand dst q = SOME w /\
  stmt_state_rel H ctx func cenv cx fin q /\
  storage_well_formed_on cx fin (FST H) /\
  immutable_frame_mods func cenv cx fin q /\
  wb_frame cenv es fin sa s0 q /\
  (~expr_has_effect e ==> pure_frame cenv func es sa s0 q) ==>
  storage_place_observed H (StoragePlace tr w etv) /\
  vv_post_mods H ctx func cenv cx e es sa sb s0 fin tv vv q /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) fin tv vv q
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `off = (case bd of Fixed _ => 0 | Dynamic _ => 1) + Num i * type_slot_size etv` >>
  `off = (case bd of Fixed _ => 0 | Dynamic _ => 1) + Num i * type_slot_size etv` by
    simp[Abbr `off`] >>
  conj_tac
  >- (irule array_slot_element_observed >> qexistsl [`bd`,`i`] >> simp[Abbr `off`]) >>
  reverse conj_tac
  >- (irule vv_store_bound_nonmem >> Cases_on `tr` >> simp[mk_ptr_def, slot_loc_def]) >>
  drule_all array_slot_element_region >> strip_tac >>
  qpat_x_assum `off = _` kall_tac >>
  `storage_holds cx tr et (PlaceR (StoragePlace tr (slot + n2w off) etv))
     (slot + n2w off) fin q` by
    (irule array_slot_element_holds >> asm_rewrite_tac[] >>
     qexistsl [`H`,`cenv`,`ctx`,`func`] >> asm_rewrite_tac[]) >>
  qpat_x_assum `wb_frame _ _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  Cases_on `tr` >>
  simp[vv_post_mods_def, vv_holds_mods_def, vv_holds_def, vv_at_def,
      vv_place_ptr_mods_def, vv_place_ptr_def, slot_loc_def, mk_ptr_def, expr_type_def] >>
  first_assum ACCEPT_TAC
QED
