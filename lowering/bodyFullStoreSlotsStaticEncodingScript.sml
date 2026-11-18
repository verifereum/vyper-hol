Theory bodyFullStoreSlotsStaticEncoding
Ancestors
  vyperEncodeDecode vyperTyping vyperStorage vyperValue venomState list
  vfmState words combin arithmetic
Libs
  wordsLib

(* Nonemptiness is propagated along the encoder's own recursion. *)
Theorem slots_encoding_nonempty[local]:
  (!tv v. !ws. encode_value tv v = SOME ws /\ value_has_type tv v /\
      type_slot_size tv <> 0 ==> ws <> []) /\
  (!off tvs vs. !ws. encode_tuple off tvs vs = SOME ws /\
      values_have_types tvs vs /\ type_slot_size_list tvs <> 0 ==> ws <> []) /\
  (!tv off sparse. !ws n. encode_static_array tv off sparse = SOME ws /\
      sparse_has_type tv n sparse /\ sparse <> [] /\ type_slot_size tv <> 0 ==>
      ws <> []) /\
  (!tv off vs. !ws. encode_dyn_array tv off vs = SOME ws /\
      all_have_type tv vs /\ vs <> [] /\ type_slot_size tv <> 0 ==> ws <> []) /\
  (!off ftypes fields. !ws. encode_struct off ftypes fields = SOME ws /\
      struct_has_type ftypes fields /\ type_slot_size_fields ftypes <> 0 ==>
      ws <> [])
Proof
  ho_match_mp_tac encode_value_ind >> rpt conj_tac >> rpt gen_tac >>
  CONV_TAC (ONCE_REWRITE_CONV [encode_value_def]) >>
  simp[AllCaseEqs()] >> rpt strip_tac >>
  gvs[value_has_type_def, type_slot_size_def, encode_dyn_bytes_slots_def,
      AllCaseEqs()] >>
  spose_not_then strip_assume_tac >> gvs[]
  >- (`sparse = []` by metis_tac[] >>
      `defaults <> []` by metis_tac[default_value_well_typed] >>
      gvs[FLAT_EQ_NIL, EVERY_GENLIST] >>
      first_x_assum (qspec_then `0` mp_tac) >> simp[])
QED

Theorem slots_encoding_positive_support:
  value_has_type tv v /\ encode_value tv v = SOME writes /\
  type_slot_size tv <> 0 ==>
  ?j. MEM j (MAP FST writes) /\ j < type_slot_size tv
Proof
  strip_tac >>
  `writes <> []` by metis_tac[slots_encoding_nonempty] >>
  Cases_on `writes` >> gvs[] >>
  qexists_tac `FST h` >> simp[] >>
  metis_tac[CONJUNCT1 encode_writes_bounded, MEM, MAP]
QED

(* The accumulator is arbitrary, but every source word comes from s. *)
Theorem slots_fold_selected_acc[local]:
  !ks q.
    (!k. MEM k ks ==> k < dimword (:256)) /\ j < dimword (:256) ==>
    (if tr then tload else sload) (dw+n2w j)
      (FOLDL (\a k. (if tr then tstore else sstore) (dw+n2w k)
        (mload (w2n (sw:bytes32)+32*k) s) a) q ks) =
    if MEM j ks then mload (w2n (sw:bytes32)+32*j) s
    else (if tr then tload else sload) (dw+n2w j) q
Proof
  Induct_on `ks` >> simp[FOLDL] >> rpt strip_tac >>
  first_x_assum (qspec_then
    `(if tr then tstore else sstore) (dw+n2w h)
      (mload (w2n (sw:bytes32)+32*h) s) q` mp_tac) >>
  (impl_tac >- simp[]) >> disch_then assume_tac >> gvs[] >>
  Cases_on `MEM j ks` >> simp[] >>
  Cases_on `j = h` >> gvs[] >>
  Cases_on `tr` >>
  simp[sload_def, sstore_def, contract_storage_def,
       tload_def, tstore_def, contract_transient_def,
       lookup_account_def, lookup_storage_def, update_storage_def,
       APPLY_UPDATE_THM]
QED

Theorem slots_fold_selected_key:
  (!k. MEM k ks <=> MEM k (MAP FST writes)) /\
  (!k. MEM k (MAP FST writes) ==> k < type_slot_size tv) /\
  w2n dw + type_slot_size tv <= dimword (:256) /\
  MEM j (MAP FST writes) ==>
  (if tr then tload else sload) (dw+n2w j)
    (FOLDL (\q k. (if tr then tstore else sstore) (dw+n2w k)
      (mload (w2n (sw:bytes32)+32*k) s) q) s ks) =
  mload (w2n (sw:bytes32)+32*j) s
Proof
  strip_tac >>
  mp_tac slots_fold_selected_acc >>
  disch_then (qspecl_then [`ks`,`s`] mp_tac) >>
  impl_tac >- (conj_tac >> rpt strip_tac >>
    `type_slot_size tv <= dimword (:256)` by decide_tac >>
    metis_tac[LESS_LESS_EQ_TRANS]) >>
  simp[]
QED
