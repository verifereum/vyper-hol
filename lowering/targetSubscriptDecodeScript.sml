(* Successful decoding along actual write-target paths. *)
Theory targetSubscriptDecode
Ancestors
  vyperStorage vyperStorageBackend vyperState vyperStorageReadSoundness
  targetPlaceLive vyperStoragePlaceProvenance words arithmetic list rich_list
  vyperInterpreter vyperAST vyperPureExpr exprSimAttributeFields

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

Theorem target_decode_value_wrapped:
  decode_value raw (w2n (slot + n2w delta : bytes32)) tv =
  decode_value raw (w2n slot + delta) tv
Proof
  irule (cj 1 decode_value_n2w) >>
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

Theorem target_extend_result_decodable:
  contract_storage_well_formed cx st /\
  target_result_decodable cx st pv /\
  extend_place cx pv sb st = (INL pv',st') ==>
  target_result_decodable cx st pv'
Proof
  Cases_on `pv` >> simp[extend_place_def, raise_def, target_result_decodable_def]
  >- (Cases_on `p` >>
      simp[extend_place_def, bind_def, ignore_bind_def, return_def, raise_def,
           AllCaseEqs()] >> rpt strip_tac >> gvs[]
      >~ [`extend_storage_place _ _ _ _ _ _`]
      >- (gvs[target_result_decodable_def] >>
          drule vyperPlaceFramesTheory.extend_storage_place_state >>
          strip_tac >> gvs[] >>
          drule_all target_storage_extend_decodable >> simp[]) >>
      simp[extend_memory_place_def, target_result_decodable_def]) >>
  Cases_on `sb` >> simp[extend_place_def, raise_def] >> Cases_on `v` >>
  simp[extend_place_def, bind_def, lift_option_type_def, return_def, raise_def,
       AllCaseEqs()] >> rpt strip_tac >>
  gvs[target_result_decodable_def, vyperMiscTheory.option_CASE_rator,
      return_def, raise_def, AllCaseEqs()] >>
  drule storage_mapping_region_step >>
  disch_then (qspec_then `v'` assume_tac) >>
  simp[] >> rpt strip_tac >>
  irule target_mapping_leaf_decodable >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem target_eval_base_decodable:
  !bt cx st pv st'.
    contract_storage_well_formed cx st /\
    EVERY pure_expr (target_indices bt) /\
    eval_base_place cx bt st = (INL pv,st') ==>
    target_result_decodable cx st pv
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac
  >~ [`eval_base_place cx (TopLevelNameTarget p) st`]
  >- (PairCases_on `p` >>
      simp[target_indices_def, Once evaluate_def, bind_def, AllCaseEqs(),
           get_scopes_def, type_check_def, assert_def, ignore_bind_def,
           return_def, raise_def] >> rpt strip_tac >> gvs[] >>
      simp[target_result_decodable_def] >>
      metis_tac[target_lookup_global_decodable]) >>
  simp[target_indices_def, Once evaluate_def, bind_def, AllCaseEqs(),
       get_scopes_def, type_check_def, assert_def, ignore_bind_def,
       return_def, raise_def] >> rpt strip_tac >> gvs[] >>
  simp[target_result_decodable_def] >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
  simp[expr_size_def] >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  drule_all nested_pop_eval_base_pure_state >> strip_tac >> gvs[]
  >~ [`pure_expr e`]
  >- (drule_all eval_expr_preserves_state >> strip_tac >> gvs[] >>
      drule read_result_state >> strip_tac >> gvs[] >>
      drule_all target_extend_result_decodable >> simp[]) >>
  drule_all target_extend_result_decodable >> simp[]
QED

Theorem target_eval_base_header_capacity:
  contract_storage_well_formed cx st /\
  EVERY pure_expr (target_indices bt) /\
  eval_base_place cx bt st =
    (INL (PlaceR (StoragePlace tr slot (ArrayTV etv (Dynamic cnt)))),st') ==>
  w2n (lookup_storage slot (get_storage cx st tr)) <= cnt
Proof
  strip_tac >> drule_all target_eval_base_decodable >>
  simp[target_result_decodable_def] >> strip_tac >>
  drule target_storage_decodable_capacity >> simp[]
QED

Theorem target_subscript_pure_capacity:
  contract_storage_well_formed cx es0 /\
  EVERY pure_expr (target_indices bt) /\ pure_expr e /\
  eval_base_place cx bt es0 =
    (INL (PlaceR (StoragePlace tr slot
      (ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)))),es1) /\
  eval_expr cx e es1 = (INL iv,es2) /\
  read_result cx iv es2 = (INL key,es) ==>
  (dyn ==> w2n (lookup_storage slot (get_storage cx es tr)) <= cnt)
Proof
  rpt strip_tac >> gvs[] >>
  drule_all nested_pop_eval_base_pure_state >> strip_tac >> gvs[] >>
  drule_all eval_expr_preserves_state >> strip_tac >> gvs[] >>
  drule read_result_state >> strip_tac >> gvs[] >>
  drule_all target_eval_base_header_capacity >> simp[]
QED
