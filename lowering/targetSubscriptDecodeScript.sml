(* Successful decoding along actual write-target paths. *)
Theory targetSubscriptDecode
Ancestors
  vyperStorage vyperStorageBackend vyperState vyperStorageReadSoundness
  targetPlaceLive vyperStoragePlaceProvenance words arithmetic list rich_list

Theorem target_decode_static_child:
  !n raw off tv vs j.
    decode_static_array raw off tv n = SOME vs /\ j < n ==>
    ?v. decode_value raw (off + j * type_slot_size tv) tv = SOME v
Proof
  Induct >> simp[Once decode_value_def] >> rpt strip_tac >>
  gvs[Once decode_value_def, AllCaseEqs()] >>
  Cases_on `j` >> gvs[MULT_CLAUSES, ADD_CLAUSES] >>
  first_x_assum drule_all >> pure_rewrite_tac[ADD_ASSOC] >>
  disch_then ACCEPT_TAC
QED

Theorem target_decode_dynamic_child:
  !n raw off tv vs j.
    decode_dyn_array raw off tv n = SOME vs /\ j < n ==>
    ?v. decode_value raw (off + j * type_slot_size tv) tv = SOME v
Proof
  Induct >> simp[Once decode_value_def] >> rpt strip_tac >>
  gvs[Once decode_value_def, AllCaseEqs()] >>
  Cases_on `j` >> gvs[MULT_CLAUSES, ADD_CLAUSES] >>
  first_x_assum drule_all >> pure_rewrite_tac[ADD_ASSOC] >>
  disch_then ACCEPT_TAC
QED

Theorem target_decode_tuple_child:
  !tvs raw off vs j.
    decode_tuple raw off tvs = SOME vs /\ j < LENGTH tvs ==>
    ?v. decode_value raw (off + tuple_prefix_slot_size j tvs)
      (EL j tvs) = SOME v
Proof
  Induct >> simp[Once decode_value_def] >> rpt strip_tac >>
  gvs[Once decode_value_def, AllCaseEqs()] >>
  Cases_on `j` >> gvs[tuple_prefix_slot_size_def] >>
  first_x_assum drule_all >> pure_rewrite_tac[ADD_ASSOC] >>
  disch_then ACCEPT_TAC
QED

Theorem target_storage_decodable_capacity:
  read_storage_slot cx tr slot (ArrayTV etv (Dynamic cnt)) st = (INL v,st) ==>
  w2n (lookup_storage slot (get_storage cx st tr)) <= cnt
Proof
  simp[read_storage_slot_def, get_storage_backend_eq, bind_def,
       lift_option_def, return_def, AllCaseEqs()] >>
  simp[Once decode_value_def, read_slot_def, AllCaseEqs()] >>
  rpt strip_tac >>
  spose_not_then assume_tac >> gvs[raise_def]
QED

Theorem target_decode_struct_child:
  !fields raw off vs id delta tv.
    decode_struct raw off fields = SOME vs /\
    struct_field_slot fields id = SOME (delta,tv) ==>
    ?v. decode_value raw (off + delta) tv = SOME v
Proof
  Induct >> simp[Once decode_value_def, struct_field_slot_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[Once decode_value_def, struct_field_slot_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  PairCases_on `z` >> gvs[] >>
  first_x_assum drule_all >>
  simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]
QED

Definition target_result_decodable_def:
  target_result_decodable cx st (PlaceR (StoragePlace tr slot tv)) =
    (?v. read_storage_slot cx tr slot tv st = (INL v,st)) /\
  target_result_decodable cx st (PlaceR _) = T /\
  target_result_decodable cx st (HashMapRef tr slot kt vt) =
    storage_mapping_region cx tr slot (HashMapT kt vt) /\
  target_result_decodable cx st (Value _) = T
End

Theorem target_lookup_global_decodable:
  contract_storage_well_formed cx st /\
  lookup_global cx mid name st = (INL pv,st') ==>
  target_result_decodable cx st pv
Proof
  Cases_on `pv` >> simp[target_result_decodable_def]
  >- (Cases_on `p` >> simp[target_result_decodable_def] >> strip_tac >>
      drule lookup_global_storage_region >> strip_tac >>
      drule_all current_declared_storage_region_read_typed >> metis_tac[]) >>
  strip_tac >> drule lookup_global_mapping_region >> simp[]
QED

Theorem target_mapping_leaf_decodable:
  contract_storage_well_formed cx st /\
  storage_mapping_region cx tr slot (Type typ) /\
  evaluate_type (get_tenv cx) typ = SOME tv ==>
  ?v. read_storage_slot cx tr slot tv st = (INL v,st)
Proof
  strip_tac >>
  qpat_x_assum `storage_mapping_region _ _ _ _` mp_tac >>
  rewrite_tac[storage_mapping_region_def] >> strip_tac >>
  first_x_assum (qspecl_then [`[]`,`slot`,`tv`] mp_tac) >>
  simp[vyperStorageLayoutSafetyTheory.resolve_hashmap_leaf_def] >> strip_tac >>
  drule_all current_declared_storage_region_read_typed >> metis_tac[]
QED

Theorem target_slot_offset_add:
  (n2w off : bytes32) = n2w off' ==>
  (n2w (off + k) : bytes32) = n2w (off' + k)
Proof
  strip_tac >> pure_rewrite_tac[GSYM word_add_n2w] >> asm_rewrite_tac[]
QED

Theorem target_read_slots_cong:
  !n raw off off'. (n2w off : bytes32) = n2w off' ==>
    read_slots raw off n = read_slots raw off' n
Proof
  Induct >> simp_tac bool_ss [read_slots_def] >> rpt gen_tac >> strip_tac >>
  asm_rewrite_tac[] >> AP_TERM_TAC >> first_x_assum irule >>
  irule target_slot_offset_add >> asm_rewrite_tac[]
QED

Theorem target_decode_bytes_cong:
  (n2w off : bytes32) = n2w off' ==>
  decode_dyn_bytes raw off mx = decode_dyn_bytes raw off' mx
Proof
  strip_tac >> asm_rewrite_tac[decode_dyn_bytes_def] >>
  `!n. read_slots raw (off + 1) n = read_slots raw (off' + 1) n` by
    (gen_tac >> irule target_read_slots_cong >>
     irule target_slot_offset_add >> asm_rewrite_tac[]) >> asm_rewrite_tac[]
QED

Theorem target_decode_offset_cong:
  (!raw off tv. !off'. (n2w off : bytes32) = n2w off' ==>
    decode_value raw off tv = decode_value raw off' tv) /\
  (!raw off tvs. !off'. (n2w off : bytes32) = n2w off' ==>
    decode_tuple raw off tvs = decode_tuple raw off' tvs) /\
  (!raw off tv n. !off'. (n2w off : bytes32) = n2w off' ==>
    decode_static_array raw off tv n = decode_static_array raw off' tv n) /\
  (!raw off tv n. !off'. (n2w off : bytes32) = n2w off' ==>
    decode_dyn_array raw off tv n = decode_dyn_array raw off' tv n) /\
  (!raw off fs. !off'. (n2w off : bytes32) = n2w off' ==>
    decode_struct raw off fs = decode_struct raw off' fs)
Proof
  ho_match_mp_tac decode_value_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >>
  drule target_decode_bytes_cong >> disch_then assume_tac >>
  asm_simp_tac bool_ss [Ntimes decode_value_def 2, read_slot_def,
    GSYM word_add_n2w, target_decode_bytes_cong] >>
  rpt (first_x_assum drule_all >> disch_then assume_tac) >>
  asm_rewrite_tac[]
  >- (simp_tac bool_ss [LET_THM] >> IF_CASES_TAC
      >- (first_x_assum (qspec_then `w2n (read_slot raw off)` mp_tac) >>
          asm_simp_tac bool_ss [read_slot_def] >>
          disch_then (qspec_then `off' + 1` mp_tac) >>
          asm_simp_tac bool_ss [GSYM word_add_n2w] >>
          disch_then (fn th => rewrite_tac[th])) >>
      asm_rewrite_tac[]) >>
  Cases_on `decode_value raw off' tv` >>
  asm_simp_tac bool_ss [optionTheory.option_case_def] >>
  first_x_assum drule >>
  disch_then (qspec_then `off' + type_slot_size tv` mp_tac) >>
  asm_simp_tac bool_ss [GSYM word_add_n2w] >>
  disch_then (fn th => rewrite_tac[th])
QED

Theorem target_decode_value_wrapped:
  decode_value raw (w2n (slot + n2w delta : bytes32)) tv =
  decode_value raw (w2n slot + delta) tv
Proof
  irule (cj 1 target_decode_offset_cong) >>
  pure_rewrite_tac[n2w_w2n, GSYM word_add_n2w] >>
  rewrite_tac[n2w_w2n]
QED

Theorem target_storage_extend_decodable:
  read_storage_slot cx tr slot tv st = (INL v,st) /\
  extend_storage_place cx tr slot tv sb st = (INL p,st') ==>
  target_result_decodable cx st' (PlaceR p)
Proof
  Cases_on `sb`
  >~ [`AttrSubscript id`]
  >- (Cases_on `tv` >> simp[extend_storage_place_def, raise_def] >>
      suspend "struct") >>
  rename1 `ValueSubscript key` >> Cases_on `key` >> Cases_on `tv` >>
  simp[extend_storage_place_def, raise_def]
  >~ [`TupleTV l`] >- suspend "tuple" >>
  Cases_on `b` >- suspend "fixed" >> suspend "dynamic"
QED

Resume target_storage_extend_decodable[struct]:
  simp[bind_def, lift_option_type_def, return_def, raise_def,
       vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  rpt strip_tac >> PairCases_on `x` >> gvs[] >>
  gvs[read_storage_slot_def, get_storage_backend_eq, bind_def,
      lift_option_def, vyperMiscTheory.option_CASE_rator,
      return_def, raise_def, AllCaseEqs()] >>
  gvs[Once decode_value_def, AllCaseEqs()] >>
  drule_all target_decode_struct_child >> strip_tac >>
  simp[target_result_decodable_def, read_storage_slot_def,
       get_storage_backend_eq, bind_def, lift_option_def, return_def,
       target_decode_value_wrapped] >>
  gvs[AC ADD_ASSOC ADD_COMM, return_def]
QED

Resume target_storage_extend_decodable[tuple]:
  simp[bind_def, ignore_bind_def, check_def, assert_def,
           lift_option_type_def, return_def, raise_def,
           vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
      rpt strip_tac >> gvs[listTheory.oEL_EQ_EL] >>
      gvs[read_storage_slot_def, get_storage_backend_eq, bind_def,
          lift_option_def, vyperMiscTheory.option_CASE_rator,
          return_def, raise_def, AllCaseEqs()] >>
      gvs[Once decode_value_def, AllCaseEqs()] >>
      drule_all target_decode_tuple_child >> strip_tac >>
      simp[target_result_decodable_def, read_storage_slot_def,
           get_storage_backend_eq, bind_def, lift_option_def, return_def,
           target_decode_value_wrapped] >>
      gvs[AC ADD_ASSOC ADD_COMM, return_def]
QED

Resume target_storage_extend_decodable[fixed]:
  simp[Once resolve_array_element_def, bind_def, ignore_bind_def,
       check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[resolve_array_element_empty, vyperMiscTheory.prod_CASE_rator,
      return_def, AllCaseEqs()] >>
  gvs[read_storage_slot_def, get_storage_backend_eq, bind_def,
      lift_option_def, vyperMiscTheory.option_CASE_rator,
      return_def, raise_def, AllCaseEqs()] >>
  gvs[Once decode_value_def, AllCaseEqs()] >>
  drule_all target_decode_static_child >> strip_tac >>
  simp[target_result_decodable_def, read_storage_slot_def,
       get_storage_backend_eq, bind_def, lift_option_def, return_def,
       target_decode_value_wrapped] >>
  gvs[AC ADD_ASSOC ADD_COMM, return_def]
QED

Resume target_storage_extend_decodable[dynamic]:
  simp[Once resolve_array_element_def, bind_def, ignore_bind_def,
       check_def, assert_def, return_def, raise_def, get_storage_backend_eq,
       AllCaseEqs()] >> rpt strip_tac >>
  gvs[resolve_array_element_empty, vyperMiscTheory.prod_CASE_rator,
      return_def, AllCaseEqs()] >>
  gvs[read_storage_slot_def, get_storage_backend_eq, bind_def,
      lift_option_def, vyperMiscTheory.option_CASE_rator,
      return_def, raise_def, AllCaseEqs()] >>
  gvs[Once decode_value_def, read_slot_def, AllCaseEqs()] >>
  `MIN (w2n (lookup_storage slot (get_storage cx s'' tr))) n =
     w2n (lookup_storage slot (get_storage cx s'' tr))` by
    (rw[MIN_DEF] >> decide_tac) >> gvs[] >>
  drule_all target_decode_dynamic_child >> strip_tac >>
  simp[target_result_decodable_def, read_storage_slot_def,
       get_storage_backend_eq, bind_def, lift_option_def, return_def,
       target_decode_value_wrapped] >>
  qpat_x_assum `decode_value _ _ _ = SOME _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp_tac bool_ss [AC ADD_ASSOC ADD_COMM] >> strip_tac >>
  asm_simp_tac bool_ss [optionTheory.option_case_def, return_def] >>
  qexists_tac `v` >> REFL_TAC
QED

Finalise target_storage_extend_decodable
