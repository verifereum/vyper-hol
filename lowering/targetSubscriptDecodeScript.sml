(* Successful decoding along actual write-target paths. *)
Theory targetSubscriptDecode
Ancestors
  vyperStorage vyperStorageBackend vyperState vyperStorageReadSoundness
  targetPlaceLive words arithmetic list rich_list

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
