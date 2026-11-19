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

Theorem target_result_decodable_trace[simp]:
  target_result_decodable cx (st with storage_trace := obs) pv =
  target_result_decodable cx st pv
Proof
  Cases_on `pv` >> simp[target_result_decodable_def] >>
  Cases_on `p` >> simp[target_result_decodable_def] >>
  simp[read_storage_slot_def, vyperStorageBackendTheory.get_storage_backend_eq,
       bind_def, lift_option_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> CASE_TAC >> simp[raise_def, return_def]
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
