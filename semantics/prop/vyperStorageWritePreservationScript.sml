(* Primitive typed storage-write preservation. *)

Theory vyperStorageWritePreservation
Ancestors
  vyperStorageLayoutSafety vyperStorageFrame vyperLookupStorage
  vyperTyping vyperState vyperStorageBackend
Libs
  wordsLib dep_rewrite

(* A successful typed primitive write establishes decodability of the exact
   region it replaces. *)
Theorem typed_write_storage_slot_establishes_region:
  value_has_type tv v /\
  well_formed_type_value tv /\
  write_storage_slot cx b slot tv v st = (INL (),st') ==>
  slots_in_range (get_storage cx st' b) (w2n slot) tv
Proof
  rpt strip_tac >>
  gvs[vyperStorageBackendTheory.write_storage_slot_eq, AllCaseEqs()] >>
  simp[vyperStorageBackendTheory.get_storage_after_set] >>
  `slots_in_range
     (apply_writes (n2w (w2n slot)) writes (get_storage cx st b))
     (w2n slot) tv` by
    (irule encode_implies_slots_in_range >> simp[] >>
     qexists `v` >> simp[]) >>
  gvs[wordsTheory.n2w_w2n]
QED


Theorem slots_in_range_disjoint_apply_writes_words[local]:
  slots_in_range storage (w2n slot2) tv2 /\
  (!wr_off. MEM wr_off (MAP FST writes) ==> wr_off < sz1) /\
  ranges_disjoint (w2n slot1) sz1
                  (w2n slot2) (type_slot_size tv2) ==>
  slots_in_range (apply_writes slot1 writes storage) (w2n slot2) tv2
Proof
  rpt strip_tac >>
  `slot1 = n2w (w2n slot1)` by simp[wordsTheory.n2w_w2n] >>
  pop_assum SUBST1_TAC >>
  irule slots_in_range_disjoint_apply_writes >>
  fs[ranges_disjoint_def] >>
  qexists `sz1` >> simp[]
QED

(* A successful typed write preserves a disjoint region on the same backend,
   and every region on the other backend. *)
Theorem typed_write_storage_slot_preserves_disjoint_region:
  slots_in_range (get_storage cx st b2) (w2n slot2) tv2 /\
  value_has_type tv1 v /\
  write_storage_slot cx b1 slot1 tv1 v st = (INL (),st') /\
  (b1 <> b2 \/
   ranges_disjoint (w2n slot1) (type_slot_size tv1)
                   (w2n slot2) (type_slot_size tv2)) ==>
  slots_in_range (get_storage cx st' b2) (w2n slot2) tv2
Proof
  rpt strip_tac >>
  gvs[vyperStorageBackendTheory.write_storage_slot_eq, AllCaseEqs()] >>
  Cases_on `b1` >> Cases_on `b2` >>
  gvs[vyperStorageBackendTheory.get_storage_after_set,
      vyperStorageBackendTheory.get_storage_after_set_other] >>
  irule slots_in_range_disjoint_apply_writes_words >>
  simp[] >>
  metis_tac[CONJUNCT1 vyperEncodeDecodeTheory.encode_writes_bounded]
QED

Theorem w2n_add_n2w_no_wrap[local]:
  w2n (bs:bytes32) + k < dimword(:256) ==>
  w2n (bs + n2w k) = w2n bs + k
Proof
  simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w,
       arithmeticTheory.MOD_LESS]
QED


Theorem array_index_element_end_bound[local]:
  i < n ==> i * sz + sz <= n * sz
Proof
  strip_tac >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  qexists `(i + 1) * sz` >>
  simp[arithmeticTheory.LEFT_ADD_DISTRIB, arithmeticTheory.ADD_COMM,
       arithmeticTheory.LESS_MONO_MULT]
QED

Theorem fixed_array_child_region_bounds:
  w2n (base_slot:bytes32) + type_slot_size (ArrayTV tv (Fixed n)) <=
    dimword(:256) /\
  i < n ==>
  w2n (base_slot + n2w (i * type_slot_size tv)) =
    w2n base_slot + i * type_slot_size tv /\
  w2n base_slot <= w2n (base_slot + n2w (i * type_slot_size tv)) /\
  w2n (base_slot + n2w (i * type_slot_size tv)) + type_slot_size tv <=
    w2n base_slot + type_slot_size (ArrayTV tv (Fixed n)) /\
  w2n (base_slot + n2w (i * type_slot_size tv)) + type_slot_size tv <=
    dimword(:256)
Proof
  rpt strip_tac >>
  `i * type_slot_size tv + type_slot_size tv <=
   n * type_slot_size tv` by
    (irule array_index_element_end_bound >> simp[]) >>
  `w2n base_slot + (i * type_slot_size tv + type_slot_size tv) <=
   dimword(:256)` by gvs[vyperValueTheory.type_slot_size_def] >>
  `w2n base_slot + i * type_slot_size tv < dimword(:256)` by
    ((Cases_on `type_slot_size tv` >-
        (pure_rewrite_tac [arithmeticTheory.MULT_CLAUSES,
                           arithmeticTheory.ADD_CLAUSES] >>
         MATCH_ACCEPT_TAC wordsTheory.w2n_lt)) >>
     gvs[] >> decide_tac) >>
  `w2n (base_slot + n2w (i * type_slot_size tv)) =
   w2n base_slot + i * type_slot_size tv` by
    (irule w2n_add_n2w_no_wrap >> simp[]) >>
  simp[] >> gvs[vyperValueTheory.type_slot_size_def]
QED


Theorem dynamic_array_child_region_bounds:
  w2n (base_slot:bytes32) + type_slot_size (ArrayTV tv (Dynamic n)) <=
    dimword(:256) /\
  0 < type_slot_size tv /\
  i < n ==>
  w2n (base_slot + n2w (1 + i * type_slot_size tv)) =
    w2n base_slot + 1 + i * type_slot_size tv /\
  w2n base_slot <=
    w2n (base_slot + n2w (1 + i * type_slot_size tv)) /\
  w2n (base_slot + n2w (1 + i * type_slot_size tv)) +
      type_slot_size tv <=
    w2n base_slot + type_slot_size (ArrayTV tv (Dynamic n)) /\
  w2n (base_slot + n2w (1 + i * type_slot_size tv)) +
      type_slot_size tv <= dimword(:256)
Proof
  rpt strip_tac >>
  `i * type_slot_size tv + type_slot_size tv <=
   n * type_slot_size tv` by
    (irule array_index_element_end_bound >> simp[]) >>
  `w2n base_slot + (1 + i * type_slot_size tv + type_slot_size tv) <=
   dimword(:256)` by gvs[vyperValueTheory.type_slot_size_def] >>
  `w2n base_slot + (1 + i * type_slot_size tv) < dimword(:256)` by
    decide_tac >>
  `w2n (base_slot + n2w (1 + i * type_slot_size tv)) =
   w2n base_slot + (1 + i * type_slot_size tv)` by
    (irule w2n_add_n2w_no_wrap >> simp[]) >>
  simp[] >> gvs[vyperValueTheory.type_slot_size_def]
QED


Theorem static_slots_in_range_index:
  static_slots_in_range storage off tv n /\ i < n ==>
  slots_in_range storage (off + i * type_slot_size tv) tv
Proof
  qid_spec_tac `i` >> qid_spec_tac `off` >> Induct_on `n` >>
  simp[slots_in_range_def] >>
  rpt strip_tac >> Cases_on `i` >> gvs[] >>
  first_x_assum
    (qspecl_then [`off + type_slot_size tv`, `n'`] assume_tac) >>
  gvs[] >>
  `off + SUC n' * type_slot_size tv =
   off + type_slot_size tv + n' * type_slot_size tv` by
    (once_rewrite_tac [arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  gvs[]
QED

Theorem dyn_slots_in_range_index:
  dyn_slots_in_range storage off tv n /\ i < n ==>
  slots_in_range storage (off + i * type_slot_size tv) tv
Proof
  qid_spec_tac `i` >> qid_spec_tac `off` >> Induct_on `n` >>
  simp[slots_in_range_def] >>
  rpt strip_tac >> Cases_on `i` >> gvs[] >>
  first_x_assum
    (qspecl_then [`off + type_slot_size tv`, `n'`] assume_tac) >>
  gvs[] >>
  `off + SUC n' * type_slot_size tv =
   off + type_slot_size tv + n' * type_slot_size tv` by
    (once_rewrite_tac [arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  gvs[]
QED

Theorem static_slots_in_range_reconstruct:
  (!j. j < n ==>
       slots_in_range storage (off + j * type_slot_size tv) tv) ==>
  static_slots_in_range storage off tv n
Proof
  qid_spec_tac `off` >> Induct_on `n` >>
  simp[slots_in_range_def] >> rpt strip_tac >>
  `slots_in_range storage off tv` by
    (qpat_x_assum `!x. _ ==> static_slots_in_range _ _ _ _` kall_tac >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[] >>
  first_x_assum irule >> rpt strip_tac >>
  qpat_x_assum
    `!k. k < SUC n ==>
         slots_in_range storage (off + k * type_slot_size tv) tv`
    (qspec_then `SUC j` mp_tac) >> simp[] >>
  `off + SUC j * type_slot_size tv =
   off + type_slot_size tv + j * type_slot_size tv` by
    (once_rewrite_tac [arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  gvs[]
QED

Theorem dyn_slots_in_range_reconstruct:
  (!j. j < n ==>
       slots_in_range storage (off + j * type_slot_size tv) tv) ==>
  dyn_slots_in_range storage off tv n
Proof
  qid_spec_tac `off` >> Induct_on `n` >>
  simp[slots_in_range_def] >> rpt strip_tac >>
  `slots_in_range storage off tv` by
    (qpat_x_assum `!x. _ ==> dyn_slots_in_range _ _ _ _` kall_tac >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[] >>
  first_x_assum irule >> rpt strip_tac >>
  qpat_x_assum
    `!k. k < SUC n ==>
         slots_in_range storage (off + k * type_slot_size tv) tv`
    (qspec_then `SUC j` mp_tac) >> simp[] >>
  `off + SUC j * type_slot_size tv =
   off + type_slot_size tv + j * type_slot_size tv` by
    (once_rewrite_tac [arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  gvs[]
QED

Theorem static_slots_in_range_reconstruct_selected:
  i < n /\
  slots_in_range storage (off + i * type_slot_size tv) tv /\
  (!j. j < n /\ j <> i ==>
       slots_in_range storage (off + j * type_slot_size tv) tv) ==>
  static_slots_in_range storage off tv n
Proof
  rpt strip_tac >> irule static_slots_in_range_reconstruct >>
  rpt strip_tac >> Cases_on `j = i` >> gvs[]
QED

Theorem dyn_slots_in_range_reconstruct_selected:
  i < n /\
  slots_in_range storage (off + i * type_slot_size tv) tv /\
  (!j. j < n /\ j <> i ==>
       slots_in_range storage (off + j * type_slot_size tv) tv) ==>
  dyn_slots_in_range storage off tv n
Proof
  rpt strip_tac >> irule dyn_slots_in_range_reconstruct >>
  rpt strip_tac >> Cases_on `j = i` >> gvs[]
QED

Theorem evaluate_type_ArrayTV_inv:
  evaluate_type tenv ty = SOME (ArrayTV tv bd) ==>
  ?elem_ty.
    ty = ArrayT elem_ty bd /\
    evaluate_type tenv elem_ty = SOME tv /\
    0 < type_slot_size tv /\
    type_slot_size (ArrayTV tv bd) < dimword(:256)
Proof
  Cases_on `ty` >>
  simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem resolve_array_element_leaf_type:
  !cx b base tv subs st slot final_tv rsubs st'.
    resolve_array_element cx b base tv subs st =
      (INL (slot, final_tv, rsubs), st') ==>
    leaf_type tv subs = leaf_type final_tv rsubs
Proof
  ho_match_mp_tac resolve_array_element_ind >> rw[] >>
  qpat_x_assum `resolve_array_element _ _ _ _ _ _ = _` mp_tac >>
  simp[Once resolve_array_element_def, bind_def, return_def, raise_def] >>
  rpt (CASE_TAC >>
       gvs[return_def, raise_def, bind_def, check_def, type_check_def,
           assert_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  gvs[assert_def, bind_def, ignore_bind_def, return_def, raise_def,
      AllCaseEqs()] >>
  imp_res_tac get_storage_backend_state >> gvs[leaf_type_def] >>
  FIRST
    [first_x_assum (qspec_then `0` mp_tac) >>
     simp[] >> disch_then drule >> simp[],
     first_x_assum (qspec_then `1` mp_tac) >>
     simp[] >> disch_then drule >> simp[]]
QED

Theorem resolve_array_element_preserves_well_formed_type:
  !cx b base tv subs st slot final_tv rsubs st'.
    resolve_array_element cx b base tv subs st =
      (INL (slot, final_tv, rsubs), st') /\
    well_formed_type_value tv ==>
    well_formed_type_value final_tv
Proof
  ho_match_mp_tac resolve_array_element_ind >> rw[] >>
  qpat_x_assum `resolve_array_element _ _ _ _ _ _ = _` mp_tac >>
  simp[Once resolve_array_element_def, bind_def, return_def, raise_def] >>
  rpt (CASE_TAC >>
       gvs[return_def, raise_def, bind_def, check_def, type_check_def,
           assert_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  gvs[assert_def, bind_def, ignore_bind_def, return_def, raise_def,
      AllCaseEqs()] >>
  imp_res_tac get_storage_backend_state >>
  gvs[well_formed_type_value_def] >>
  FIRST
    [first_x_assum (qspec_then `0` mp_tac) >>
     simp[] >> disch_then drule >> simp[],
     first_x_assum (qspec_then `1` mp_tac) >>
     simp[] >> disch_then drule >> simp[]]
QED

Theorem resolve_array_element_state_local[local]:
  !cx b base tv subs st res st'.
    resolve_array_element cx b base tv subs st = (res, st') ==> st' = st
Proof
  ho_match_mp_tac resolve_array_element_ind >> rw[] >>
  qpat_x_assum `_ = (res, st')` mp_tac >>
  simp[Once resolve_array_element_def, bind_def, return_def, raise_def] >>
  rpt (CASE_TAC >>
       gvs[return_def, raise_def, bind_def, check_def, type_check_def,
           assert_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  gvs[assert_def, bind_def, ignore_bind_def, return_def, raise_def,
      AllCaseEqs()] >>
  imp_res_tac get_storage_backend_state >> gvs[] >>
  FIRST [first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
         disch_then drule >> simp[],
         first_x_assum (qspec_then `1` mp_tac) >> simp[] >>
         disch_then drule >> simp[]]
QED



Theorem resolve_array_element_preserves_contract_storage_well_formed[local]:
  !cx b root_slot tv subs st res st'.
    contract_storage_well_formed cx st /\
    resolve_array_element cx b root_slot tv subs st = (res,st') ==>
    contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  irule contract_storage_well_formed_storage_frame >>
  imp_res_tac resolve_array_element_state_local >>
  qexists `st` >> simp[]
QED

Theorem resolve_array_element_region_bounds:
  !cx is_transient base tv subs st.
    !slot final_tv rsubs st' tenv ty.
    evaluate_type tenv ty = SOME tv /\
    w2n (base:bytes32) + type_slot_size tv <= dimword(:256) /\
    resolve_array_element cx is_transient base tv subs st =
      (INL (slot, final_tv, rsubs), st') ==>
    w2n base <= w2n slot /\
    w2n slot + type_slot_size final_tv <=
      w2n base + type_slot_size tv /\
    w2n slot + type_slot_size final_tv <= dimword(:256)
Proof
  ho_match_mp_tac resolve_array_element_ind >> rw[] >>
  qpat_x_assum `resolve_array_element _ _ _ _ _ _ = _` mp_tac >>
  simp[Once resolve_array_element_def, bind_def, return_def, raise_def] >>
  rpt (CASE_TAC >>
       gvs[return_def, raise_def, bind_def, check_def, type_check_def,
           assert_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  gvs[assert_def, bind_def, ignore_bind_def, return_def, raise_def,
      AllCaseEqs()] >>
  imp_res_tac evaluate_type_ArrayTV_inv >>
  rpt
    (FIRST
      [qpat_assum `evaluate_type _ _ = SOME (ArrayTV _ (Fixed _))`
         (K all_tac) >>
       `w2n (base' + n2w (Num idx * type_slot_size tv)) =
          w2n base' + Num idx * type_slot_size tv /\
        w2n base' <= w2n (base' + n2w (Num idx * type_slot_size tv)) /\
        w2n (base' + n2w (Num idx * type_slot_size tv)) +
          type_slot_size tv <=
          w2n base' + type_slot_size (ArrayTV tv (Fixed n)) /\
        w2n (base' + n2w (Num idx * type_slot_size tv)) +
          type_slot_size tv <= dimword(:256)` by
         (irule fixed_array_child_region_bounds >> simp[]) >>
       qpat_x_assum
         `!elem_offset st slot final_tv rsubs st' tenv ty. _`
         (qspecl_then
            [`0`, `s''`, `slot`, `final_tv`, `rsubs`, `st'`, `tenv`, `elem_ty`]
            mp_tac) >>
       simp[] >> strip_tac >> decide_tac,
       qpat_assum `evaluate_type _ _ = SOME (ArrayTV _ (Dynamic _))`
         (K all_tac) >>
       `w2n (base' + n2w (1 + Num idx * type_slot_size tv)) =
          w2n base' + 1 + Num idx * type_slot_size tv /\
        w2n base' <=
          w2n (base' + n2w (1 + Num idx * type_slot_size tv)) /\
        w2n (base' + n2w (1 + Num idx * type_slot_size tv)) +
          type_slot_size tv <=
          w2n base' + type_slot_size (ArrayTV tv (Dynamic n)) /\
        w2n (base' + n2w (1 + Num idx * type_slot_size tv)) +
          type_slot_size tv <= dimword(:256)` by
         (irule dynamic_array_child_region_bounds >> simp[]) >>
       qpat_x_assum
         `!elem_offset st slot final_tv rsubs st' tenv ty. _`
         (qspecl_then
            [`1`, `s''`, `slot`, `final_tv`, `rsubs`, `st'`, `tenv`, `elem_ty`]
            mp_tac) >>
       simp[] >> strip_tac >> decide_tac])
QED

Theorem contained_array_child_disjoint_sibling[local]:
  0 < sz /\ (i < j \/ j < i) /\
  off + (i * sz + sz) <= dimword(:256) /\
  off + (j * sz + sz) <= dimword(:256) /\
  off + i * sz <= leaf /\
  leaf + leaf_sz <= off + (i * sz + sz) ==>
  ranges_disjoint leaf leaf_sz (off + j * sz) sz
Proof
  rpt strip_tac
  >- (`i * sz + sz <= j * sz` by
        (irule array_index_element_end_bound >> decide_tac) >>
      rewrite_tac[ranges_disjoint_def] >>
      conj_tac
      >- (irule arithmeticTheory.LESS_EQ_TRANS >>
          qexists `off + (i * sz + sz)` >>
          conj_tac >- first_assum ACCEPT_TAC >>
          first_assum ACCEPT_TAC) >>
      conj_tac
      >- (SUBST1_TAC
            (GSYM (Q.SPECL [`off`, `j * sz`, `sz`] arithmeticTheory.ADD_ASSOC)) >>
          first_assum ACCEPT_TAC) >>
      disj1_tac >>
      irule arithmeticTheory.LESS_EQ_TRANS >>
      qexists `off + (i * sz + sz)` >>
      conj_tac >- first_assum ACCEPT_TAC >>
      decide_tac)
  >> `j * sz + sz <= i * sz` by
       (irule array_index_element_end_bound >> decide_tac) >>
  rewrite_tac[ranges_disjoint_def] >>
  conj_tac
  >- (irule arithmeticTheory.LESS_EQ_TRANS >>
      qexists `off + (i * sz + sz)` >>
      conj_tac >- first_assum ACCEPT_TAC >>
      first_assum ACCEPT_TAC) >>
  conj_tac
  >- (SUBST1_TAC
        (GSYM (Q.SPECL [`off`, `j * sz`, `sz`]
                        arithmeticTheory.ADD_ASSOC)) >>
      first_assum ACCEPT_TAC) >>
  disj2_tac >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  qexists `off + (j * sz + sz)` >>
  conj_tac >- decide_tac >>
  decide_tac
QED

Theorem contained_dynamic_child_disjoint_header[local]:
  0 < sz /\ off + 1 <= leaf /\
  leaf + leaf_sz <= dimword(:256) /\ off + 1 <= dimword(:256) ==>
  ranges_disjoint leaf leaf_sz off 1
Proof
  simp[ranges_disjoint_def] >> decide_tac
QED

Theorem apply_writes_lookup_other_raw[local]:
  !writes (base : bytes32) storage (addr : bytes32).
    (!off. MEM off (MAP FST writes) ==>
           n2w (w2n base + off) <> addr) ==>
    lookup_storage addr (apply_writes base writes storage) =
      lookup_storage addr storage
Proof
  Induct >> simp[vyperStorageTheory.apply_writes_def] >>
  Cases >> simp[vyperStorageTheory.apply_writes_def] >>
  rpt strip_tac >>
  simp[vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM]
QED

Theorem nwn_eq_apply_writes_raw[local]:
  !(base : num) k.
    n2w (w2n (n2w base : bytes32) + k) = n2w (base + k) : bytes32
Proof
  rewrite_tac[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n]
QED

Theorem read_slot_disjoint_apply_writes_num[local]:
  (!wr_off. MEM wr_off (MAP FST writes) ==> wr_off < sz1) ==>
  ranges_disjoint off1 sz1 read_off 1 ==>
  read_slot (apply_writes (n2w off1) writes storage) read_off =
    read_slot storage read_off
Proof
  rpt strip_tac >>
  simp[vyperStorageTheory.read_slot_def] >>
  irule apply_writes_lookup_other_raw >>
  rewrite_tac[nwn_eq_apply_writes_raw] >>
  rpt strip_tac >>
  `off < sz1` by res_tac >>
  gvs[ranges_disjoint_def, wordsTheory.n2w_11]
QED

Theorem typed_write_storage_slot_preserves_disjoint_read_slot[local]:
  value_has_type tv v ==>
  write_storage_slot cx b slot tv v st = (INL (), st') ==>
  ranges_disjoint (w2n slot) (type_slot_size tv) off 1 ==>
  read_slot (get_storage cx st' b) off = read_slot (get_storage cx st b) off
Proof
  rpt strip_tac >>
  gvs[vyperStorageBackendTheory.write_storage_slot_eq, AllCaseEqs()] >>
  simp[vyperStorageBackendTheory.get_storage_after_set] >>
  `slot = n2w (w2n slot)` by simp[wordsTheory.n2w_w2n] >>
  pop_assum SUBST1_TAC >>
  irule read_slot_disjoint_apply_writes_num >>
  simp[] >>
  metis_tac[CONJUNCT1 vyperEncodeDecodeTheory.encode_writes_bounded]
QED

Theorem typed_write_storage_slot_preserves_disjoint_num_region[local]:
  slots_in_range (get_storage cx st b2) off2 tv2 ==>
  value_has_type tv1 v ==>
  write_storage_slot cx b1 slot1 tv1 v st = (INL (), st') ==>
  off2 < dimword(:256) ==>
  (b1 <> b2 \/
   ranges_disjoint (w2n slot1) (type_slot_size tv1)
                   off2 (type_slot_size tv2)) ==>
  slots_in_range (get_storage cx st' b2) off2 tv2
Proof
  rpt strip_tac >>
  gvs[vyperStorageBackendTheory.write_storage_slot_eq, AllCaseEqs()] >>
  Cases_on `b1` >> Cases_on `b2` >>
  gvs[vyperStorageBackendTheory.get_storage_after_set,
      vyperStorageBackendTheory.get_storage_after_set_other] >>
  `slot1 = n2w (w2n slot1)` by simp[wordsTheory.n2w_w2n] >>
  pop_assum SUBST1_TAC >>
  irule slots_in_range_disjoint_apply_writes >>
  fs[ranges_disjoint_def] >>
  qexists `type_slot_size tv1` >> simp[] >>
  metis_tac[CONJUNCT1 vyperEncodeDecodeTheory.encode_writes_bounded]
QED

Theorem typed_two_writes_preserve_disjoint_num_region[local]:
  slots_in_range (get_storage cx st b2) off2 tv2 ==>
  value_has_type tv1 v1 ==>
  write_storage_slot cx b1 slot1 tv1 v1 st = (INL (), st1) ==>
  value_has_type tv3 v3 ==>
  write_storage_slot cx b3 slot3 tv3 v3 st1 = (INL (), st2) ==>
  off2 < dimword(:256) ==>
  (b1 <> b2 \/
   ranges_disjoint (w2n slot1) (type_slot_size tv1)
                   off2 (type_slot_size tv2)) ==>
  (b3 <> b2 \/
   ranges_disjoint (w2n slot3) (type_slot_size tv3)
                   off2 (type_slot_size tv2)) ==>
  slots_in_range (get_storage cx st2 b2) off2 tv2
Proof
  rpt strip_tac >>
  `slots_in_range (get_storage cx st1 b2) off2 tv2` by
    (irule typed_write_storage_slot_preserves_disjoint_num_region >>
     simp[] >>
     qexistsl [`b1`, `slot1`, `st`, `tv1`, `v1`] >> simp[]) >>
  irule typed_write_storage_slot_preserves_disjoint_num_region >>
  simp[] >>
  qexistsl [`b3`, `slot3`, `st1`, `tv3`, `v3`] >> simp[]
QED

Theorem typed_two_writes_preserve_disjoint_read_slot[local]:
  value_has_type tv1 v1 ==>
  write_storage_slot cx b slot1 tv1 v1 st = (INL (), st1) ==>
  value_has_type tv2 v2 ==>
  write_storage_slot cx b slot2 tv2 v2 st1 = (INL (), st2) ==>
  ranges_disjoint (w2n slot1) (type_slot_size tv1) off 1 ==>
  ranges_disjoint (w2n slot2) (type_slot_size tv2) off 1 ==>
  read_slot (get_storage cx st2 b) off = read_slot (get_storage cx st b) off
Proof
  rpt strip_tac >>
  `read_slot (get_storage cx st1 b) off =
   read_slot (get_storage cx st b) off` by
    (irule typed_write_storage_slot_preserves_disjoint_read_slot >> simp[] >>
     qexistsl [`slot1`, `tv1`, `v1`] >> simp[]) >>
  `read_slot (get_storage cx st2 b) off =
   read_slot (get_storage cx st1 b) off` by
    (irule typed_write_storage_slot_preserves_disjoint_read_slot >> simp[] >>
     qexistsl [`slot2`, `tv2`, `v2`] >> simp[]) >>
  simp[]
QED

Theorem fixed_array_typed_leaf_write_reconstruct[local]:
  slots_in_range (get_storage cx st b) off (ArrayTV tv (Fixed n)) /\
  i < n /\
  0 < type_slot_size tv /\
  off + type_slot_size (ArrayTV tv (Fixed n)) <= dimword(:256) /\
  off + i * type_slot_size tv <= w2n slot /\
  w2n slot + type_slot_size final_tv <=
    off + (i * type_slot_size tv + type_slot_size tv) /\
  value_has_type final_tv v /\
  write_storage_slot cx b slot final_tv v st = (INL (), st') /\
  slots_in_range (get_storage cx st' b)
    (off + i * type_slot_size tv) tv ==>
  slots_in_range (get_storage cx st' b) off (ArrayTV tv (Fixed n))
Proof
  rpt strip_tac >>
  fs[slots_in_range_def] >>
  `!j. j < n /\ j <> i ==>
       slots_in_range (get_storage cx st' b)
         (off + j * type_slot_size tv) tv` by
    (rpt strip_tac >>
     `slots_in_range (get_storage cx st b)
        (off + j * type_slot_size tv) tv` by
       (irule static_slots_in_range_index >> qexists `n` >> simp[]) >>
     `j * type_slot_size tv + type_slot_size tv <=
      n * type_slot_size tv` by
       (irule array_index_element_end_bound >> simp[]) >>
     `i * type_slot_size tv + type_slot_size tv <=
      n * type_slot_size tv` by
       (irule array_index_element_end_bound >> simp[]) >>
     `off + (i * type_slot_size tv + type_slot_size tv) <=
      dimword(:256)` by
       gvs[vyperValueTheory.type_slot_size_def] >>
     `off + (j * type_slot_size tv + type_slot_size tv) <=
      dimword(:256)` by
       gvs[vyperValueTheory.type_slot_size_def] >>
     `off + j * type_slot_size tv < dimword(:256)` by decide_tac >>
     `ranges_disjoint (w2n slot) (type_slot_size final_tv)
        (off + j * type_slot_size tv) (type_slot_size tv)` by
       (irule contained_array_child_disjoint_sibling >>
        conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qexists `i` >> simp[] >>
        gvs[vyperValueTheory.type_slot_size_def] >>
        decide_tac) >>
     drule typed_write_storage_slot_preserves_disjoint_num_region >>
     disch_then drule >>
     disch_then drule >>
     disch_then drule >>
     disch_then irule >>
     simp[]) >>
  irule static_slots_in_range_reconstruct_selected >>
  qexists `i` >> simp[]
QED

Theorem dynamic_array_typed_leaf_write_reconstruct[local]:
  slots_in_range (get_storage cx st b) off (ArrayTV tv (Dynamic max)) /\
  i < w2n (read_slot (get_storage cx st b) off) /\
  0 < type_slot_size tv /\
  off + type_slot_size (ArrayTV tv (Dynamic max)) <= dimword(:256) /\
  off + 1 + i * type_slot_size tv <= w2n slot /\
  w2n slot + type_slot_size final_tv <=
    off + 1 + (i * type_slot_size tv + type_slot_size tv) /\
  value_has_type final_tv v /\
  write_storage_slot cx b slot final_tv v st = (INL (), st') /\
  slots_in_range (get_storage cx st' b)
    (off + 1 + i * type_slot_size tv) tv ==>
  slots_in_range (get_storage cx st' b) off (ArrayTV tv (Dynamic max))
Proof
  rpt strip_tac >>
  qabbrev_tac `len = w2n (read_slot (get_storage cx st b) off)` >>
  `len <= max` by
    (qpat_x_assum
       `slots_in_range _ off (ArrayTV tv (Dynamic max))` mp_tac >>
     simp[slots_in_range_def, Abbr `len`]) >>
  `MIN len max = len` by
    (simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  `dyn_slots_in_range (get_storage cx st b) (off + 1) tv len` by
    (qpat_x_assum
       `slots_in_range _ off (ArrayTV tv (Dynamic max))` mp_tac >>
     simp[slots_in_range_def, Abbr `len`]) >>
  `i * type_slot_size tv + type_slot_size tv <=
   max * type_slot_size tv` by
    (irule array_index_element_end_bound >> decide_tac) >>
  `off + 1 + (i * type_slot_size tv + type_slot_size tv) <=
   dimword(:256)` by gvs[vyperValueTheory.type_slot_size_def] >>
  `read_slot (get_storage cx st' b) off =
   read_slot (get_storage cx st b) off` by
    (drule typed_write_storage_slot_preserves_disjoint_read_slot >>
     disch_then drule >>
     disch_then irule >>
     irule contained_dynamic_child_disjoint_header >>
     gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `!j. j < len /\ j <> i ==>
       slots_in_range (get_storage cx st' b)
         (off + 1 + j * type_slot_size tv) tv` by
    (rpt strip_tac >>
     `slots_in_range (get_storage cx st b)
        (off + 1 + j * type_slot_size tv) tv` by
       (irule dyn_slots_in_range_index >> qexists `len` >> simp[]) >>
     `j * type_slot_size tv + type_slot_size tv <=
      max * type_slot_size tv` by
       (irule arithmeticTheory.LESS_EQ_TRANS >>
        qexists `(j + 1) * type_slot_size tv` >>
        simp[arithmeticTheory.LEFT_ADD_DISTRIB,
             arithmeticTheory.LESS_MONO_MULT]) >>
     `i * type_slot_size tv + type_slot_size tv <=
      max * type_slot_size tv` by
       (irule arithmeticTheory.LESS_EQ_TRANS >>
        qexists `(i + 1) * type_slot_size tv` >>
        simp[arithmeticTheory.LEFT_ADD_DISTRIB,
             arithmeticTheory.LESS_MONO_MULT]) >>
     `off + 1 + (i * type_slot_size tv + type_slot_size tv) <=
      dimword(:256)` by gvs[vyperValueTheory.type_slot_size_def] >>
     `off + 1 + (j * type_slot_size tv + type_slot_size tv) <=
      dimword(:256)` by gvs[vyperValueTheory.type_slot_size_def] >>
     `off + 1 + j * type_slot_size tv < dimword(:256)` by decide_tac >>
     `ranges_disjoint (w2n slot) (type_slot_size final_tv)
        (off + 1 + j * type_slot_size tv) (type_slot_size tv)` by
       (irule contained_array_child_disjoint_sibling >>
        conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qexists `i` >> simp[] >> decide_tac) >>
     drule typed_write_storage_slot_preserves_disjoint_num_region >>
     disch_then drule >>
     disch_then drule >>
     disch_then drule >>
     disch_then irule >> simp[]) >>
  `dyn_slots_in_range (get_storage cx st' b) (off + 1) tv len` by
    (irule dyn_slots_in_range_reconstruct_selected >>
     qexists `i` >> simp[]) >>
  simp[slots_in_range_def, Abbr `len`] >> gvs[]
QED

Theorem fixed_array_typed_leaf_write_reconstruct_curried[local]:
  slots_in_range (get_storage cx st b) off (ArrayTV tv (Fixed n)) ==>
  i < n ==>
  0 < type_slot_size tv ==>
  off + type_slot_size (ArrayTV tv (Fixed n)) <= dimword(:256) ==>
  child_off = off + i * type_slot_size tv ==>
  child_off <= w2n slot ==>
  w2n slot + type_slot_size final_tv <= child_off + type_slot_size tv ==>
  value_has_type final_tv v ==>
  write_storage_slot cx b slot final_tv v st = (INL (), st') ==>
  slots_in_range (get_storage cx st' b) child_off tv ==>
  slots_in_range (get_storage cx st' b) off (ArrayTV tv (Fixed n))
Proof
  rpt strip_tac >> gvs[] >>
  irule fixed_array_typed_leaf_write_reconstruct >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >>
  qexistsl [`final_tv`, `i`, `slot`, `st`, `v`] >> simp[]
QED

Theorem dynamic_array_typed_leaf_write_reconstruct_curried[local]:
  slots_in_range (get_storage cx st b) off (ArrayTV tv (Dynamic max)) ==>
  i < w2n (read_slot (get_storage cx st b) off) ==>
  0 < type_slot_size tv ==>
  off + type_slot_size (ArrayTV tv (Dynamic max)) <= dimword(:256) ==>
  child_off = off + 1 + i * type_slot_size tv ==>
  child_off <= w2n slot ==>
  w2n slot + type_slot_size final_tv <= child_off + type_slot_size tv ==>
  value_has_type final_tv v ==>
  write_storage_slot cx b slot final_tv v st = (INL (), st') ==>
  slots_in_range (get_storage cx st' b) child_off tv ==>
  slots_in_range (get_storage cx st' b) off (ArrayTV tv (Dynamic max))
Proof
  rpt strip_tac >> gvs[] >>
  irule dynamic_array_typed_leaf_write_reconstruct >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >>
  qexistsl [`final_tv`, `i`, `slot`, `st`, `v`] >> simp[]
QED


Theorem fixed_array_two_typed_leaf_writes_reconstruct_curried[local]:
  slots_in_range (get_storage cx st b) off (ArrayTV tv (Fixed n)) ==>
  i < n ==>
  0 < type_slot_size tv ==>
  off + type_slot_size (ArrayTV tv (Fixed n)) <= dimword(:256) ==>
  child_off = off + i * type_slot_size tv ==>
  child_off <= w2n slot1 ==>
  w2n slot1 + type_slot_size tv1 <= child_off + type_slot_size tv ==>
  value_has_type tv1 v1 ==>
  write_storage_slot cx b slot1 tv1 v1 st = (INL (), st1) ==>
  child_off <= w2n slot2 ==>
  w2n slot2 + type_slot_size tv2 <= child_off + type_slot_size tv ==>
  value_has_type tv2 v2 ==>
  write_storage_slot cx b slot2 tv2 v2 st1 = (INL (), st2) ==>
  slots_in_range (get_storage cx st2 b) child_off tv ==>
  slots_in_range (get_storage cx st2 b) off (ArrayTV tv (Fixed n))
Proof
  rpt strip_tac >> gvs[] >>
  fs[slots_in_range_def] >>
  `!j. j < n /\ j <> i ==>
       slots_in_range (get_storage cx st2 b)
         (off + j * type_slot_size tv) tv` by
    (rpt strip_tac >>
     `slots_in_range (get_storage cx st b)
        (off + j * type_slot_size tv) tv` by
       (irule static_slots_in_range_index >> qexists `n` >> simp[]) >>
     `j * type_slot_size tv + type_slot_size tv <=
      n * type_slot_size tv` by
       (irule array_index_element_end_bound >> simp[]) >>
     `i * type_slot_size tv + type_slot_size tv <=
      n * type_slot_size tv` by
       (irule array_index_element_end_bound >> simp[]) >>
     `off + (i * type_slot_size tv + type_slot_size tv) <=
      dimword(:256)` by
       gvs[vyperValueTheory.type_slot_size_def] >>
     `off + (j * type_slot_size tv + type_slot_size tv) <=
      dimword(:256)` by
       gvs[vyperValueTheory.type_slot_size_def] >>
     `off + j * type_slot_size tv < dimword(:256)` by decide_tac >>
     `ranges_disjoint (w2n slot1) (type_slot_size tv1)
        (off + j * type_slot_size tv) (type_slot_size tv)` by
       (irule contained_array_child_disjoint_sibling >>
        conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qexists `i` >> simp[] >>
        gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
     `ranges_disjoint (w2n slot2) (type_slot_size tv2)
        (off + j * type_slot_size tv) (type_slot_size tv)` by
       (irule contained_array_child_disjoint_sibling >>
        conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qexists `i` >> simp[] >>
        gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
     irule typed_two_writes_preserve_disjoint_num_region >>
     simp[] >>
     qexistsl [`b`, `b`, `slot1`, `slot2`, `st`, `st1`, `tv1`, `tv2`,
                `v1`, `v2`] >> simp[]) >>
  irule static_slots_in_range_reconstruct_selected >>
  qexists `i` >> simp[]
QED

Theorem dynamic_array_two_typed_leaf_writes_reconstruct_curried[local]:
  slots_in_range (get_storage cx st b) off (ArrayTV tv (Dynamic max)) ==>
  i < w2n (read_slot (get_storage cx st b) off) ==>
  0 < type_slot_size tv ==>
  off + type_slot_size (ArrayTV tv (Dynamic max)) <= dimword(:256) ==>
  child_off = off + 1 + i * type_slot_size tv ==>
  child_off <= w2n slot1 ==>
  w2n slot1 + type_slot_size tv1 <= child_off + type_slot_size tv ==>
  value_has_type tv1 v1 ==>
  write_storage_slot cx b slot1 tv1 v1 st = (INL (), st1) ==>
  child_off <= w2n slot2 ==>
  w2n slot2 + type_slot_size tv2 <= child_off + type_slot_size tv ==>
  value_has_type tv2 v2 ==>
  write_storage_slot cx b slot2 tv2 v2 st1 = (INL (), st2) ==>
  slots_in_range (get_storage cx st2 b) child_off tv ==>
  slots_in_range (get_storage cx st2 b) off (ArrayTV tv (Dynamic max))
Proof
  rpt strip_tac >> gvs[] >>
  qabbrev_tac `len = w2n (read_slot (get_storage cx st b) off)` >>
  `len <= max` by
    (qpat_x_assum
       `slots_in_range _ off (ArrayTV tv (Dynamic max))` mp_tac >>
     simp[slots_in_range_def, Abbr `len`]) >>
  `MIN len max = len` by
    (simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  `dyn_slots_in_range (get_storage cx st b) (off + 1) tv len` by
    (qpat_x_assum
       `slots_in_range _ off (ArrayTV tv (Dynamic max))` mp_tac >>
     simp[slots_in_range_def, Abbr `len`]) >>
  `i * type_slot_size tv + type_slot_size tv <=
   max * type_slot_size tv` by
    (irule array_index_element_end_bound >> decide_tac) >>
  `off + 1 + (i * type_slot_size tv + type_slot_size tv) <=
   dimword(:256)` by gvs[vyperValueTheory.type_slot_size_def] >>
  `ranges_disjoint (w2n slot1) (type_slot_size tv1) off 1` by
    (irule contained_dynamic_child_disjoint_header >>
     gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `ranges_disjoint (w2n slot2) (type_slot_size tv2) off 1` by
    (irule contained_dynamic_child_disjoint_header >>
     gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `read_slot (get_storage cx st2 b) off =
   read_slot (get_storage cx st b) off` by
    (irule typed_two_writes_preserve_disjoint_read_slot >> simp[] >>
     qexistsl [`slot1`, `slot2`, `st1`, `tv1`, `tv2`, `v1`, `v2`] >>
     simp[]) >>
  `!j. j < len /\ j <> i ==>
       slots_in_range (get_storage cx st2 b)
         (off + 1 + j * type_slot_size tv) tv` by
    (rpt strip_tac >>
     `slots_in_range (get_storage cx st b)
        (off + 1 + j * type_slot_size tv) tv` by
       (irule dyn_slots_in_range_index >> qexists `len` >> simp[]) >>
     `j * type_slot_size tv + type_slot_size tv <=
      max * type_slot_size tv` by
       (irule arithmeticTheory.LESS_EQ_TRANS >>
        qexists `(j + 1) * type_slot_size tv` >>
        simp[arithmeticTheory.LEFT_ADD_DISTRIB,
             arithmeticTheory.LESS_MONO_MULT]) >>
     `i * type_slot_size tv + type_slot_size tv <=
      max * type_slot_size tv` by
       (irule arithmeticTheory.LESS_EQ_TRANS >>
        qexists `(i + 1) * type_slot_size tv` >>
        simp[arithmeticTheory.LEFT_ADD_DISTRIB,
             arithmeticTheory.LESS_MONO_MULT]) >>
     `off + 1 + (i * type_slot_size tv + type_slot_size tv) <=
      dimword(:256)` by gvs[vyperValueTheory.type_slot_size_def] >>
     `off + 1 + (j * type_slot_size tv + type_slot_size tv) <=
      dimword(:256)` by gvs[vyperValueTheory.type_slot_size_def] >>
     `off + 1 + j * type_slot_size tv < dimword(:256)` by decide_tac >>
     `ranges_disjoint (w2n slot1) (type_slot_size tv1)
        (off + 1 + j * type_slot_size tv) (type_slot_size tv)` by
       (irule contained_array_child_disjoint_sibling >>
        conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qexists `i` >> simp[] >> decide_tac) >>
     `ranges_disjoint (w2n slot2) (type_slot_size tv2)
        (off + 1 + j * type_slot_size tv) (type_slot_size tv)` by
       (irule contained_array_child_disjoint_sibling >>
        conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qexists `i` >> simp[] >> decide_tac) >>
     `off + (j * type_slot_size tv + 1) =
      off + 1 + j * type_slot_size tv` by decide_tac >>
     irule typed_two_writes_preserve_disjoint_num_region >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`b`, `b`, `slot1`, `slot2`, `st`, `st1`, `tv1`, `tv2`,
                `v1`, `v2`] >> simp[]) >>
  `dyn_slots_in_range (get_storage cx st2 b) (off + 1) tv len` by
    (irule dyn_slots_in_range_reconstruct_selected >>
     qexists `i` >> simp[]) >>
  simp[slots_in_range_def, Abbr `len`] >> gvs[]
QED
Definition resolver_array_children_positive_def[local]:
  (resolver_array_children_positive
     (ArrayTV elem_tv (Dynamic n)) (_::rest) =
     (0 < type_slot_size elem_tv /\
      resolver_array_children_positive elem_tv rest)) /\
  (resolver_array_children_positive
     (ArrayTV elem_tv (Fixed n)) (_::rest) =
     (0 < type_slot_size elem_tv /\
      resolver_array_children_positive elem_tv rest)) /\
  (resolver_array_children_positive tv subs = T)
End

Theorem evaluate_type_resolver_array_children_positive[local]:
  !subs tenv ty tv.
    evaluate_type tenv ty = SOME tv ==>
    resolver_array_children_positive tv subs
Proof
  Induct >> simp[resolver_array_children_positive_def] >>
  rpt strip_tac >> Cases_on `tv` >>
  simp[resolver_array_children_positive_def] >>
  Cases_on `b` >> simp[resolver_array_children_positive_def] >>
  imp_res_tac evaluate_type_ArrayTV_inv >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem resolve_array_element_region_bounds_positive[local]:
  !cx b base tv subs st slot final_tv rsubs st'.
    resolver_array_children_positive tv subs ==>
    well_formed_type_value tv ==>
    w2n (base:bytes32) + type_slot_size tv <= dimword(:256) ==>
    resolve_array_element cx b base tv subs st =
      (INL (slot, final_tv, rsubs), st') ==>
    w2n base <= w2n slot /\
    w2n slot + type_slot_size final_tv <=
      w2n base + type_slot_size tv /\
    w2n slot + type_slot_size final_tv <= dimword(:256)
Proof
  ho_match_mp_tac resolve_array_element_ind >> rw[] >>
  qpat_x_assum `resolve_array_element _ _ _ _ _ _ = _` mp_tac >>
  simp[Once resolve_array_element_def, bind_def, return_def, raise_def] >>
  rpt (CASE_TAC >>
       gvs[return_def, raise_def, bind_def, check_def, type_check_def,
           assert_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  gvs[assert_def, bind_def, ignore_bind_def, return_def, raise_def,
      AllCaseEqs()] >>
  imp_res_tac get_storage_backend_state >>
  gvs[resolver_array_children_positive_def, well_formed_type_value_def] >>
  rpt
    (FIRST
      [qpat_assum
         `type_slot_size (ArrayTV _ (Fixed _)) + w2n _ <= _` (K all_tac) >>
       `w2n (base' + n2w (Num idx * type_slot_size tv)) =
          w2n base' + Num idx * type_slot_size tv /\
        w2n base' <= w2n (base' + n2w (Num idx * type_slot_size tv)) /\
        w2n (base' + n2w (Num idx * type_slot_size tv)) +
          type_slot_size tv <=
          w2n base' + type_slot_size (ArrayTV tv (Fixed n)) /\
        w2n (base' + n2w (Num idx * type_slot_size tv)) +
          type_slot_size tv <= dimword(:256)` by
         (irule fixed_array_child_region_bounds >> simp[]) >>
       qpat_x_assum
         `!elem_offset st slot final_tv rsubs st'. _`
         (qspecl_then
            [`0`, `s''`, `slot`, `final_tv`, `rsubs`, `st'`] mp_tac) >>
       simp[] >> strip_tac >> decide_tac,
       qpat_assum
         `type_slot_size (ArrayTV _ (Dynamic _)) + w2n _ <= _` (K all_tac) >>
       `w2n (base' + n2w (1 + Num idx * type_slot_size tv)) =
          w2n base' + 1 + Num idx * type_slot_size tv /\
        w2n base' <=
          w2n (base' + n2w (1 + Num idx * type_slot_size tv)) /\
        w2n (base' + n2w (1 + Num idx * type_slot_size tv)) +
          type_slot_size tv <=
          w2n base' + type_slot_size (ArrayTV tv (Dynamic n)) /\
        w2n (base' + n2w (1 + Num idx * type_slot_size tv)) +
          type_slot_size tv <= dimword(:256)` by
         (irule dynamic_array_child_region_bounds >> simp[]) >>
       qpat_x_assum
         `!elem_offset st slot final_tv rsubs st'. _`
         (qspecl_then
            [`1`, `s''`, `slot`, `final_tv`, `rsubs`, `st'`] mp_tac) >>
       simp[] >> strip_tac >> decide_tac])
QED

Theorem resolve_array_element_state_local[local]:
  !cx b base tv subs st res st'.
    resolve_array_element cx b base tv subs st = (res, st') ==> st' = st
Proof
  ho_match_mp_tac resolve_array_element_ind >> rw[] >>
  qpat_x_assum `_ = (res, st')` mp_tac >>
  simp[Once resolve_array_element_def, bind_def, return_def, raise_def] >>
  rpt (CASE_TAC >>
       gvs[return_def, raise_def, bind_def, check_def, type_check_def,
           assert_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  gvs[assert_def, bind_def, ignore_bind_def, return_def, raise_def,
      AllCaseEqs()] >>
  imp_res_tac get_storage_backend_state >> gvs[] >>
  FIRST [first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
         disch_then drule >> simp[],
         first_x_assum (qspec_then `1` mp_tac) >> simp[] >>
         disch_then drule >> simp[]]
QED

Theorem typed_write_storage_slot_establishes_region_forward[local]:
  !cx b slot tv v st st'.
    write_storage_slot cx b slot tv v st = (INL (),st') ==>
    value_has_type tv v ==>
    well_formed_type_value tv ==>
    slots_in_range (get_storage cx st' b) (w2n slot) tv
Proof
  rpt strip_tac >>
  drule_at (Pat `write_storage_slot`) typed_write_storage_slot_establishes_region >>
  simp[]
QED

Theorem resolve_array_element_typed_write_preserves_root_core[local]:
  !cx b base tv subs st slot final_tv st_res v st'.
    resolver_array_children_positive tv subs /\
    well_formed_type_value tv /\
    w2n (base:bytes32) + type_slot_size tv <= dimword(:256) /\
    slots_in_range (get_storage cx st b) (w2n base) tv /\
    resolve_array_element cx b base tv subs st =
      (INL (slot, final_tv, []), st_res) /\
    value_has_type final_tv v /\
    write_storage_slot cx b slot final_tv v st_res = (INL (), st') ==>
    slots_in_range (get_storage cx st' b) (w2n base) tv
Proof
  ho_match_mp_tac resolve_array_element_ind >> rw[] >>
  qpat_x_assum `resolve_array_element _ _ _ _ _ _ = _` mp_tac >>
  simp[Once resolve_array_element_def, bind_def, return_def, raise_def] >>
  rpt (CASE_TAC >>
       gvs[return_def, raise_def, bind_def, check_def, type_check_def,
           assert_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  gvs[assert_def, bind_def, ignore_bind_def, return_def, raise_def,
      AllCaseEqs()] >>
  imp_res_tac get_storage_backend_state >>
  imp_res_tac resolve_array_element_state_local >>
  gvs[resolver_array_children_positive_def, well_formed_type_value_def,
      get_storage_backend_eq] >>~-
    ([`slots_in_range (get_storage cx st' b) (w2n base')
         (ArrayTV tv (Fixed n))`],
     `w2n (base' + n2w (Num idx * type_slot_size tv)) =
        w2n base' + Num idx * type_slot_size tv /\
      w2n base' <= w2n (base' + n2w (Num idx * type_slot_size tv)) /\
      w2n (base' + n2w (Num idx * type_slot_size tv)) + type_slot_size tv <=
        w2n base' + type_slot_size (ArrayTV tv (Fixed n)) /\
      w2n (base' + n2w (Num idx * type_slot_size tv)) + type_slot_size tv <=
        dimword(:256)` by
       (irule fixed_array_child_region_bounds >> simp[]) >>
     `slots_in_range (get_storage cx s'' b)
        (w2n base' + Num idx * type_slot_size tv) tv` by
       (irule static_slots_in_range_index >> qexists `n` >>
        gvs[slots_in_range_def]) >>
     qpat_assum `!elem_offset st slot' final_tv' st_res' v' st''. _`
       (qspecl_then
          [`0`, `s''`, `slot`, `final_tv`, `s''`, `v`, `st'`] mp_tac) >>
     simp[] >> strip_tac >>
     drule resolve_array_element_region_bounds_positive >>
     disch_then drule >> disch_then drule >> disch_then drule >> strip_tac >>
     `w2n base' + type_slot_size (ArrayTV tv (Fixed n)) <= dimword(:256)` by
       (qpat_x_assum
          `type_slot_size (ArrayTV tv (Fixed n)) + w2n base' <= _` mp_tac >>
        once_rewrite_tac [arithmeticTheory.ADD_COMM] >> simp[]) >>
     drule fixed_array_typed_leaf_write_reconstruct_curried >>
     disch_then drule >> disch_then drule >> disch_then drule >>
     disch_then drule >> disch_then drule >> disch_then drule >>
     disch_then drule >>
     disch_then (qspec_then `st'` mp_tac) >> simp[]) >>~-
    ([`slots_in_range (get_storage cx st' b) (w2n base')
         (ArrayTV tv (Dynamic n))`],
     `w2n (base' + n2w (1 + Num idx * type_slot_size tv)) =
        w2n base' + 1 + Num idx * type_slot_size tv /\
      w2n base' <= w2n (base' + n2w (1 + Num idx * type_slot_size tv)) /\
      w2n (base' + n2w (1 + Num idx * type_slot_size tv)) +
        type_slot_size tv <=
        w2n base' + type_slot_size (ArrayTV tv (Dynamic n)) /\
      w2n (base' + n2w (1 + Num idx * type_slot_size tv)) +
        type_slot_size tv <= dimword(:256)` by
       (irule dynamic_array_child_region_bounds >> simp[]) >>
     `slots_in_range (get_storage cx s'' b)
        (w2n base' + 1 + Num idx * type_slot_size tv) tv` by
       (irule dyn_slots_in_range_index >>
        qexists `w2n (read_slot (get_storage cx s'' b) (w2n base'))` >>
        gvs[slots_in_range_def, vyperStorageTheory.read_slot_def] >>
        `MIN (w2n (lookup_storage base' (get_storage cx s'' b))) n =
         w2n (lookup_storage base' (get_storage cx s'' b))` by
          (simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
        gvs[]) >>
     `base' + n2w (1 + Num idx * type_slot_size tv) =
      base' + n2w (Num idx * type_slot_size tv + 1)` by
       (AP_TERM_TAC >> AP_TERM_TAC >>
        MATCH_ACCEPT_TAC arithmeticTheory.ADD_COMM) >>
     qpat_x_assum
       `resolve_array_element cx b
          (base' + n2w (Num idx * type_slot_size tv + 1)) tv subs s'' = _`
       mp_tac >>
     qpat_x_assum
       `base' + n2w (1 + Num idx * type_slot_size tv) =
        base' + n2w (Num idx * type_slot_size tv + 1)`
       (fn th => once_rewrite_tac [GSYM th]) >>
     strip_tac >>
     qpat_assum `!elem_offset st slot' final_tv' st_res' v' st''. _`
       (qspecl_then
          [`1`, `s''`, `slot`, `final_tv`, `s''`, `v`, `st'`] mp_tac) >>
     simp[] >> strip_tac >>
     drule resolve_array_element_region_bounds_positive >>
     disch_then drule >> disch_then drule >> disch_then drule >> strip_tac >>
     `w2n base' + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256)` by
       (qpat_x_assum
          `type_slot_size (ArrayTV tv (Dynamic n)) + w2n base' <= _` mp_tac >>
        once_rewrite_tac [arithmeticTheory.ADD_COMM] >> simp[]) >>
     drule dynamic_array_typed_leaf_write_reconstruct_curried >>
     disch_then irule >> simp[] >>
     qexistsl [`final_tv`, `Num idx`, `slot`, `v`] >>
     gvs[vyperStorageTheory.read_slot_def]) >>
  drule typed_write_storage_slot_establishes_region_forward >>
  disch_then drule >> disch_then irule >>
  simp[well_formed_type_value_def]
QED


Theorem resolve_array_element_contained_write_preserves_root_core[local]:
  !cx b base tv subs st slot final_tv st_res wr_slot wr_tv wr_v st'.
    resolver_array_children_positive tv subs /\
    well_formed_type_value tv /\
    w2n (base:bytes32) + type_slot_size tv <= dimword(:256) /\
    slots_in_range (get_storage cx st b) (w2n base) tv /\
    resolve_array_element cx b base tv subs st =
      (INL (slot, final_tv, []), st_res) /\
    value_has_type wr_tv wr_v /\
    write_storage_slot cx b wr_slot wr_tv wr_v st_res = (INL (), st') /\
    w2n slot <= w2n wr_slot /\
    w2n wr_slot + type_slot_size wr_tv <=
      w2n slot + type_slot_size final_tv /\
    slots_in_range (get_storage cx st' b) (w2n slot) final_tv ==>
    slots_in_range (get_storage cx st' b) (w2n base) tv
Proof
  ho_match_mp_tac resolve_array_element_ind >> rw[] >>
  qpat_x_assum `resolve_array_element _ _ _ _ _ _ = _` mp_tac >>
  simp[Once resolve_array_element_def, bind_def, return_def, raise_def] >>
  rpt (CASE_TAC >>
       gvs[return_def, raise_def, bind_def, check_def, type_check_def,
           assert_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  gvs[assert_def, bind_def, ignore_bind_def, return_def, raise_def,
      AllCaseEqs()] >>
  imp_res_tac get_storage_backend_state >>
  imp_res_tac resolve_array_element_state_local >>
  gvs[resolver_array_children_positive_def, well_formed_type_value_def,
      get_storage_backend_eq] >>~-
    ([`slots_in_range (get_storage cx st' b) (w2n base')
         (ArrayTV tv (Fixed n))`],
     `w2n (base' + n2w (Num idx * type_slot_size tv)) =
        w2n base' + Num idx * type_slot_size tv /\
      w2n base' <= w2n (base' + n2w (Num idx * type_slot_size tv)) /\
      w2n (base' + n2w (Num idx * type_slot_size tv)) + type_slot_size tv <=
        w2n base' + type_slot_size (ArrayTV tv (Fixed n)) /\
      w2n (base' + n2w (Num idx * type_slot_size tv)) + type_slot_size tv <=
        dimword(:256)` by
       (irule fixed_array_child_region_bounds >> simp[]) >>
     `slots_in_range (get_storage cx s'' b)
        (w2n base' + Num idx * type_slot_size tv) tv` by
       (irule static_slots_in_range_index >> qexists `n` >>
        gvs[slots_in_range_def]) >>
     qpat_assum
       `!elem_offset st slot' final_tv' st_res' wr_slot' wr_tv' wr_v' st''. _`
       (qspecl_then
          [`0`, `s''`, `slot`, `final_tv`, `s''`, `wr_slot`, `wr_tv`,
           `wr_v`, `st'`] mp_tac) >>
     simp[] >> strip_tac >>
     drule resolve_array_element_region_bounds_positive >>
     disch_then drule >> disch_then drule >> disch_then drule >> strip_tac >>
     `w2n base' + type_slot_size (ArrayTV tv (Fixed n)) <= dimword(:256)` by
       (qpat_x_assum
          `type_slot_size (ArrayTV tv (Fixed n)) + w2n base' <= _` mp_tac >>
        once_rewrite_tac [arithmeticTheory.ADD_COMM] >> simp[]) >>
     `w2n base' + Num idx * type_slot_size tv <= w2n wr_slot` by
       decide_tac >>
     `w2n wr_slot + type_slot_size wr_tv <=
      w2n base' + Num idx * type_slot_size tv + type_slot_size tv` by
       decide_tac >>
     drule fixed_array_typed_leaf_write_reconstruct_curried >>
     disch_then irule >> simp[] >>
     qexistsl [`wr_tv`, `Num idx`, `wr_slot`, `wr_v`] >> simp[]) >>~-
    ([`slots_in_range (get_storage cx st' b) (w2n base')
         (ArrayTV tv (Dynamic n))`],
     `w2n (base' + n2w (1 + Num idx * type_slot_size tv)) =
        w2n base' + 1 + Num idx * type_slot_size tv /\
      w2n base' <= w2n (base' + n2w (1 + Num idx * type_slot_size tv)) /\
      w2n (base' + n2w (1 + Num idx * type_slot_size tv)) +
        type_slot_size tv <=
        w2n base' + type_slot_size (ArrayTV tv (Dynamic n)) /\
      w2n (base' + n2w (1 + Num idx * type_slot_size tv)) +
        type_slot_size tv <= dimword(:256)` by
       (irule dynamic_array_child_region_bounds >> simp[]) >>
     `slots_in_range (get_storage cx s'' b)
        (w2n base' + 1 + Num idx * type_slot_size tv) tv` by
       (irule dyn_slots_in_range_index >>
        qexists `w2n (read_slot (get_storage cx s'' b) (w2n base'))` >>
        gvs[slots_in_range_def, vyperStorageTheory.read_slot_def] >>
        `MIN (w2n (lookup_storage base' (get_storage cx s'' b))) n =
         w2n (lookup_storage base' (get_storage cx s'' b))` by
          (simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
        gvs[]) >>
     `base' + n2w (1 + Num idx * type_slot_size tv) =
      base' + n2w (Num idx * type_slot_size tv + 1)` by
       (AP_TERM_TAC >> AP_TERM_TAC >>
        MATCH_ACCEPT_TAC arithmeticTheory.ADD_COMM) >>
     qpat_x_assum
       `resolve_array_element cx b
          (base' + n2w (Num idx * type_slot_size tv + 1)) tv subs s'' = _`
       mp_tac >>
     qpat_x_assum
       `base' + n2w (1 + Num idx * type_slot_size tv) =
        base' + n2w (Num idx * type_slot_size tv + 1)`
       (fn th => once_rewrite_tac [GSYM th]) >>
     strip_tac >>
     qpat_assum
       `!elem_offset st slot' final_tv' st_res' wr_slot' wr_tv' wr_v' st''. _`
       (qspecl_then
          [`1`, `s''`, `slot`, `final_tv`, `s''`, `wr_slot`, `wr_tv`,
           `wr_v`, `st'`] mp_tac) >>
     simp[] >> strip_tac >>
     drule resolve_array_element_region_bounds_positive >>
     disch_then drule >> disch_then drule >> disch_then drule >> strip_tac >>
     `w2n base' + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256)` by
       (qpat_x_assum
          `type_slot_size (ArrayTV tv (Dynamic n)) + w2n base' <= _` mp_tac >>
        once_rewrite_tac [arithmeticTheory.ADD_COMM] >> simp[]) >>
     `w2n base' + 1 + Num idx * type_slot_size tv <= w2n wr_slot` by
       decide_tac >>
     `w2n wr_slot + type_slot_size wr_tv <=
      w2n base' + 1 + Num idx * type_slot_size tv + type_slot_size tv` by
       decide_tac >>
     drule dynamic_array_typed_leaf_write_reconstruct_curried >>
     disch_then irule >> simp[] >>
     qexistsl [`wr_tv`, `Num idx`, `wr_slot`, `wr_v`] >>
     gvs[vyperStorageTheory.read_slot_def]) >>
  first_assum ACCEPT_TAC
QED

Theorem resolve_array_element_contained_write_preserves_root:
  !cx b base tv subs st slot final_tv st_res wr_slot wr_tv wr_v st' tenv ty.
    evaluate_type tenv ty = SOME tv /\
    well_formed_type_value tv /\
    w2n (base:bytes32) + type_slot_size tv <= dimword(:256) /\
    slots_in_range (get_storage cx st b) (w2n base) tv /\
    resolve_array_element cx b base tv subs st =
      (INL (slot, final_tv, []), st_res) /\
    value_has_type wr_tv wr_v /\
    write_storage_slot cx b wr_slot wr_tv wr_v st_res = (INL (), st') /\
    w2n slot <= w2n wr_slot /\
    w2n wr_slot + type_slot_size wr_tv <=
      w2n slot + type_slot_size final_tv /\
    slots_in_range (get_storage cx st' b) (w2n slot) final_tv ==>
    slots_in_range (get_storage cx st' b) (w2n base) tv
Proof
  rpt strip_tac >>
  qspec_then `subs` drule evaluate_type_resolver_array_children_positive >>
  strip_tac >>
  irule resolve_array_element_contained_write_preserves_root_core >>
  simp[] >>
  qexistsl [`final_tv`, `slot`, `st`, `st_res`, `subs`, `wr_slot`, `wr_tv`,
             `wr_v`] >>
  simp[]
QED

Theorem resolve_array_element_two_contained_writes_preserve_root_core[local]:
  !cx b base tv subs st slot final_tv st_res
   wr_slot1 wr_tv1 wr_v1 st1 wr_slot2 wr_tv2 wr_v2 st2.
    resolver_array_children_positive tv subs /\
    well_formed_type_value tv /\
    w2n (base:bytes32) + type_slot_size tv <= dimword(:256) /\
    slots_in_range (get_storage cx st b) (w2n base) tv /\
    resolve_array_element cx b base tv subs st =
      (INL (slot, final_tv, []), st_res) /\
    value_has_type wr_tv1 wr_v1 /\
    write_storage_slot cx b wr_slot1 wr_tv1 wr_v1 st_res = (INL (), st1) /\
    w2n slot <= w2n wr_slot1 /\
    w2n wr_slot1 + type_slot_size wr_tv1 <=
      w2n slot + type_slot_size final_tv /\
    value_has_type wr_tv2 wr_v2 /\
    write_storage_slot cx b wr_slot2 wr_tv2 wr_v2 st1 = (INL (), st2) /\
    w2n slot <= w2n wr_slot2 /\
    w2n wr_slot2 + type_slot_size wr_tv2 <=
      w2n slot + type_slot_size final_tv /\
    slots_in_range (get_storage cx st2 b) (w2n slot) final_tv ==>
    slots_in_range (get_storage cx st2 b) (w2n base) tv
Proof
  ho_match_mp_tac resolve_array_element_ind >> rw[] >>
  qpat_x_assum `resolve_array_element _ _ _ _ _ _ = _` mp_tac >>
  simp[Once resolve_array_element_def, bind_def, return_def, raise_def] >>
  rpt (CASE_TAC >>
       gvs[return_def, raise_def, bind_def, check_def, type_check_def,
           assert_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  gvs[assert_def, bind_def, ignore_bind_def, return_def, raise_def,
      AllCaseEqs()] >>
  imp_res_tac get_storage_backend_state >>
  imp_res_tac resolve_array_element_state_local >>
  gvs[resolver_array_children_positive_def, well_formed_type_value_def,
      get_storage_backend_eq] >>~-
    ([`slots_in_range (get_storage cx st2 b) (w2n base')
         (ArrayTV tv (Fixed n))`],
     `w2n (base' + n2w (Num idx * type_slot_size tv)) =
        w2n base' + Num idx * type_slot_size tv /\
      w2n base' <= w2n (base' + n2w (Num idx * type_slot_size tv)) /\
      w2n (base' + n2w (Num idx * type_slot_size tv)) + type_slot_size tv <=
        w2n base' + type_slot_size (ArrayTV tv (Fixed n)) /\
      w2n (base' + n2w (Num idx * type_slot_size tv)) + type_slot_size tv <=
        dimword(:256)` by
       (irule fixed_array_child_region_bounds >> simp[]) >>
     `slots_in_range (get_storage cx s'' b)
        (w2n base' + Num idx * type_slot_size tv) tv` by
       (irule static_slots_in_range_index >> qexists `n` >>
        gvs[slots_in_range_def]) >>
     qpat_assum
       `!elem_offset st slot' final_tv' st_res'
          wr_slot1' wr_tv1' wr_v1' st1'
          wr_slot2' wr_tv2' wr_v2' st2'. _`
       (qspecl_then
          [`0`, `s''`, `slot`, `final_tv`, `s''`,
           `wr_slot1`, `wr_tv1`, `wr_v1`, `st1`,
           `wr_slot2`, `wr_tv2`, `wr_v2`, `st2`] mp_tac) >>
     simp[] >> strip_tac >>
     drule resolve_array_element_region_bounds_positive >>
     disch_then drule >> disch_then drule >> disch_then drule >> strip_tac >>
     `w2n base' + type_slot_size (ArrayTV tv (Fixed n)) <= dimword(:256)` by
       (qpat_x_assum
          `type_slot_size (ArrayTV tv (Fixed n)) + w2n base' <= _` mp_tac >>
        once_rewrite_tac [arithmeticTheory.ADD_COMM] >> simp[]) >>
     `w2n base' + Num idx * type_slot_size tv <= w2n wr_slot1` by
       decide_tac >>
     `w2n wr_slot1 + type_slot_size wr_tv1 <=
      w2n base' + Num idx * type_slot_size tv + type_slot_size tv` by
       decide_tac >>
     `w2n base' + Num idx * type_slot_size tv <= w2n wr_slot2` by
       decide_tac >>
     `w2n wr_slot2 + type_slot_size wr_tv2 <=
      w2n base' + Num idx * type_slot_size tv + type_slot_size tv` by
       decide_tac >>
     drule fixed_array_two_typed_leaf_writes_reconstruct_curried >>
     disch_then irule >> simp[] >>
     qexistsl [`Num idx`, `wr_slot1`, `wr_slot2`, `st1`,
                `wr_tv1`, `wr_tv2`, `wr_v1`, `wr_v2`] >>
     simp[]) >>~-
    ([`slots_in_range (get_storage cx st2 b) (w2n base')
         (ArrayTV tv (Dynamic n))`],
     `w2n (base' + n2w (1 + Num idx * type_slot_size tv)) =
        w2n base' + 1 + Num idx * type_slot_size tv /\
      w2n base' <= w2n (base' + n2w (1 + Num idx * type_slot_size tv)) /\
      w2n (base' + n2w (1 + Num idx * type_slot_size tv)) +
        type_slot_size tv <=
        w2n base' + type_slot_size (ArrayTV tv (Dynamic n)) /\
      w2n (base' + n2w (1 + Num idx * type_slot_size tv)) +
        type_slot_size tv <= dimword(:256)` by
       (irule dynamic_array_child_region_bounds >> simp[]) >>
     `slots_in_range (get_storage cx s'' b)
        (w2n base' + 1 + Num idx * type_slot_size tv) tv` by
       (irule dyn_slots_in_range_index >>
        qexists `w2n (read_slot (get_storage cx s'' b) (w2n base'))` >>
        gvs[slots_in_range_def, vyperStorageTheory.read_slot_def] >>
        `MIN (w2n (lookup_storage base' (get_storage cx s'' b))) n =
         w2n (lookup_storage base' (get_storage cx s'' b))` by
          (simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
        gvs[]) >>
     `base' + n2w (1 + Num idx * type_slot_size tv) =
      base' + n2w (Num idx * type_slot_size tv + 1)` by
       (AP_TERM_TAC >> AP_TERM_TAC >>
        MATCH_ACCEPT_TAC arithmeticTheory.ADD_COMM) >>
     qpat_x_assum
       `resolve_array_element cx b
          (base' + n2w (Num idx * type_slot_size tv + 1)) tv subs s'' = _`
       mp_tac >>
     qpat_x_assum
       `base' + n2w (1 + Num idx * type_slot_size tv) =
        base' + n2w (Num idx * type_slot_size tv + 1)`
       (fn th => once_rewrite_tac [GSYM th]) >>
     strip_tac >>
     qpat_assum
       `!elem_offset st slot' final_tv' st_res'
          wr_slot1' wr_tv1' wr_v1' st1'
          wr_slot2' wr_tv2' wr_v2' st2'. _`
       (qspecl_then
          [`1`, `s''`, `slot`, `final_tv`, `s''`,
           `wr_slot1`, `wr_tv1`, `wr_v1`, `st1`,
           `wr_slot2`, `wr_tv2`, `wr_v2`, `st2`] mp_tac) >>
     simp[] >> strip_tac >>
     drule resolve_array_element_region_bounds_positive >>
     disch_then drule >> disch_then drule >> disch_then drule >> strip_tac >>
     `w2n base' + type_slot_size (ArrayTV tv (Dynamic n)) <= dimword(:256)` by
       (qpat_x_assum
          `type_slot_size (ArrayTV tv (Dynamic n)) + w2n base' <= _` mp_tac >>
        once_rewrite_tac [arithmeticTheory.ADD_COMM] >> simp[]) >>
     `w2n base' + 1 + Num idx * type_slot_size tv <= w2n wr_slot1` by
       decide_tac >>
     `w2n wr_slot1 + type_slot_size wr_tv1 <=
      w2n base' + 1 + Num idx * type_slot_size tv + type_slot_size tv` by
       decide_tac >>
     `w2n base' + 1 + Num idx * type_slot_size tv <= w2n wr_slot2` by
       decide_tac >>
     `w2n wr_slot2 + type_slot_size wr_tv2 <=
      w2n base' + 1 + Num idx * type_slot_size tv + type_slot_size tv` by
       decide_tac >>
     drule dynamic_array_two_typed_leaf_writes_reconstruct_curried >>
     disch_then irule >>
     gvs[vyperStorageTheory.read_slot_def] >>
     qexistsl [`Num idx`, `wr_slot1`, `wr_slot2`, `st1`,
                `wr_tv1`, `wr_tv2`, `wr_v1`, `wr_v2`] >>
     gvs[vyperStorageTheory.read_slot_def]) >>
  first_assum ACCEPT_TAC
QED

Theorem resolve_array_element_two_contained_writes_preserve_root:
  !cx b base tv subs st slot final_tv st_res
   wr_slot1 wr_tv1 wr_v1 st1 wr_slot2 wr_tv2 wr_v2 st2 tenv ty.
    evaluate_type tenv ty = SOME tv /\
    well_formed_type_value tv /\
    w2n (base:bytes32) + type_slot_size tv <= dimword(:256) /\
    slots_in_range (get_storage cx st b) (w2n base) tv /\
    resolve_array_element cx b base tv subs st =
      (INL (slot, final_tv, []), st_res) /\
    value_has_type wr_tv1 wr_v1 /\
    write_storage_slot cx b wr_slot1 wr_tv1 wr_v1 st_res = (INL (), st1) /\
    w2n slot <= w2n wr_slot1 /\
    w2n wr_slot1 + type_slot_size wr_tv1 <=
      w2n slot + type_slot_size final_tv /\
    value_has_type wr_tv2 wr_v2 /\
    write_storage_slot cx b wr_slot2 wr_tv2 wr_v2 st1 = (INL (), st2) /\
    w2n slot <= w2n wr_slot2 /\
    w2n wr_slot2 + type_slot_size wr_tv2 <=
      w2n slot + type_slot_size final_tv /\
    slots_in_range (get_storage cx st2 b) (w2n slot) final_tv ==>
    slots_in_range (get_storage cx st2 b) (w2n base) tv
Proof
  rpt strip_tac >>
  qspec_then `subs` drule evaluate_type_resolver_array_children_positive >>
  strip_tac >>
  irule resolve_array_element_two_contained_writes_preserve_root_core >>
  simp[] >>
  qexistsl [`final_tv`, `slot`, `st`, `st1`, `st_res`, `subs`,
             `wr_slot1`, `wr_slot2`, `wr_tv1`, `wr_tv2`,
             `wr_v1`, `wr_v2`] >>
  simp[]
QED


Theorem resolve_array_element_typed_write_preserves_root:
  !cx b base tv subs st slot final_tv st_res v st' tenv ty.
    evaluate_type tenv ty = SOME tv /\
    well_formed_type_value tv /\
    w2n (base:bytes32) + type_slot_size tv <= dimword(:256) /\
    slots_in_range (get_storage cx st b) (w2n base) tv /\
    resolve_array_element cx b base tv subs st =
      (INL (slot, final_tv, []), st_res) /\
    value_has_type final_tv v /\
    write_storage_slot cx b slot final_tv v st_res = (INL (), st') ==>
    slots_in_range (get_storage cx st' b) (w2n base) tv
Proof
  rpt strip_tac >>
  qspec_then `subs` drule evaluate_type_resolver_array_children_positive >>
  strip_tac >>
  drule_at (Pat `resolve_array_element`)
    resolve_array_element_typed_write_preserves_root_core >>
  disch_then (qspecl_then [`v`, `st'`] irule) >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- (qexists `v` >> simp[]) >>
  simp[]
QED

Theorem uint256_header_write_read_exact[local]:
  len < dimword(:256) /\
  write_storage_slot cx b (n2w off) (BaseTV (UintT 256)) (IntV (&len)) st =
    (INL (), st') ==>
  read_slot (get_storage cx st' b) off = n2w len
Proof
  rpt strip_tac >>
  gvs[vyperStorageBackendTheory.write_storage_slot_eq,
      vyperStorageTheory.encode_value_def,
      vyperStorageTheory.encode_base_to_slot_def] >>
  simp[vyperStorageBackendTheory.get_storage_after_set,
       vyperStorageTheory.read_slot_def, vyperStorageTheory.apply_writes_def,
       vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM, integer_wordTheory.i2w_pos]
QED

Theorem dynamic_array_append_element_write_prefix[local]:
  slots_in_range (get_storage cx st b) off (ArrayTV tv (Dynamic max)) /\
  w2n (read_slot (get_storage cx st b) off) = len /\
  len < max /\
  0 < type_slot_size tv /\
  well_formed_type_value tv /\
  off + type_slot_size (ArrayTV tv (Dynamic max)) <= dimword(:256) /\
  value_has_type tv v /\
  write_storage_slot cx b
    (n2w (off + 1 + len * type_slot_size tv)) tv v st = (INL (), st') ==>
  slots_in_range (get_storage cx st' b) off (ArrayTV tv (Dynamic max)) /\
  slots_in_range (get_storage cx st' b)
    (off + 1 + len * type_slot_size tv) tv /\
  read_slot (get_storage cx st' b) off =
    read_slot (get_storage cx st b) off
Proof
  rpt gen_tac >> strip_tac >>
  `len <= max` by decide_tac >>
  `MIN len max = len` by simp[arithmeticTheory.MIN_DEF] >>
  `dyn_slots_in_range (get_storage cx st b) (off + 1) tv len` by
    (qpat_x_assum `slots_in_range _ off (ArrayTV tv (Dynamic max))` mp_tac >>
     simp[slots_in_range_def]) >>
  `len * type_slot_size tv + type_slot_size tv <=
   max * type_slot_size tv` by
    (irule array_index_element_end_bound >> simp[]) >>
  `off + 1 + len * type_slot_size tv + type_slot_size tv <= dimword(:256)` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `off + 1 + len * type_slot_size tv < dimword(:256)` by decide_tac >>
  `off + (type_slot_size tv + (len * type_slot_size tv + 1)) =
   off + 1 + len * type_slot_size tv + type_slot_size tv` by decide_tac >>
  `w2n (n2w (off + 1 + len * type_slot_size tv) : bytes32) =
   off + 1 + len * type_slot_size tv` by simp[] >>
  `read_slot (get_storage cx st' b) off =
   read_slot (get_storage cx st b) off` by
    (drule typed_write_storage_slot_preserves_disjoint_read_slot >>
     disch_then drule >> disch_then irule >>
     qpat_assum
       `w2n (n2w (off + 1 + len * type_slot_size tv) : bytes32) = _`
       (fn th => rewrite_tac [th]) >>
     rewrite_tac[ranges_disjoint_def] >>
     conj_tac
     >- (qpat_assum
           `off + (type_slot_size tv + (len * type_slot_size tv + 1)) = _`
           (fn th => once_rewrite_tac [th]) >>
         first_assum ACCEPT_TAC) >>
     conj_tac >- decide_tac >>
     disj2_tac >> decide_tac) >>
  `!j. j < len ==>
       slots_in_range (get_storage cx st' b)
         (off + 1 + j * type_slot_size tv) tv` by
    (rpt strip_tac >>
     `slots_in_range (get_storage cx st b)
        (off + 1 + j * type_slot_size tv) tv` by
       (irule dyn_slots_in_range_index >> qexists `len` >> simp[]) >>
     `j * type_slot_size tv + type_slot_size tv <=
      max * type_slot_size tv` by
       (irule array_index_element_end_bound >> decide_tac) >>
     `off + 1 + j * type_slot_size tv + type_slot_size tv <=
      dimword(:256)` by
       (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
     `off + 1 + j * type_slot_size tv < dimword(:256)` by decide_tac >>
     `off + (type_slot_size tv + (j * type_slot_size tv + 1)) =
      off + 1 + j * type_slot_size tv + type_slot_size tv` by decide_tac >>
     drule typed_write_storage_slot_preserves_disjoint_num_region >>
     disch_then drule >> disch_then drule >>
     disch_then drule >> disch_then irule >>
     disj2_tac >>
     qpat_assum
       `w2n (n2w (off + 1 + len * type_slot_size tv) : bytes32) = _`
       (fn th => rewrite_tac [th]) >>
     rewrite_tac[ranges_disjoint_def] >>
     conj_tac
     >- (qpat_assum
           `off + (type_slot_size tv + (len * type_slot_size tv + 1)) = _`
           (fn th => once_rewrite_tac [th]) >>
         first_assum ACCEPT_TAC) >>
     conj_tac
     >- (qpat_assum
           `off + (type_slot_size tv + (j * type_slot_size tv + 1)) = _`
           (fn th => once_rewrite_tac [th]) >>
         first_assum ACCEPT_TAC) >>
     disj2_tac >>
     `j * type_slot_size tv + type_slot_size tv <=
      len * type_slot_size tv` by
       (irule array_index_element_end_bound >> simp[]) >>
     decide_tac) >>
  conj_tac
  >- (simp[slots_in_range_def] >>
      irule dyn_slots_in_range_reconstruct >> simp[]) >>
  conj_tac
  >- (drule typed_write_storage_slot_establishes_region_forward >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Theorem dynamic_array_append_header_write_reconstruct_forward[local]:
  write_storage_slot cx b (n2w off) (BaseTV (UintT 256))
    (IntV (&(len + 1))) st = (INL (), st') ==>
  slots_in_range (get_storage cx st b) off (ArrayTV tv (Dynamic max)) ==>
  w2n (read_slot (get_storage cx st b) off) = len ==>
  len < max ==>
  0 < type_slot_size tv ==>
  off + type_slot_size (ArrayTV tv (Dynamic max)) <= dimword(:256) ==>
  slots_in_range (get_storage cx st b)
    (off + 1 + len * type_slot_size tv) tv ==>
  value_has_type (BaseTV (UintT 256)) (IntV (&(len + 1))) ==>
  slots_in_range (get_storage cx st' b) off (ArrayTV tv (Dynamic max))
Proof
  rpt strip_tac >>
  `len + 1 <= max` by decide_tac >>
  `MIN len max = len` by simp[arithmeticTheory.MIN_DEF] >>
  `len + 1 < dimword(:256)` by
    (qpat_x_assum `value_has_type _ _` mp_tac >>
     simp[value_has_type_def, integerTheory.NUM_OF_INT,
          integerTheory.INT_POS]) >>
  `off < dimword(:256)` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `w2n (n2w off : bytes32) = off` by simp[] >>
  `read_slot (get_storage cx st' b) off = n2w (len + 1)` by
    (drule_at (Pat `write_storage_slot`) uint256_header_write_read_exact >> simp[]) >>
  `!j. j < len + 1 ==>
       slots_in_range (get_storage cx st' b)
         (off + 1 + j * type_slot_size tv) tv` by
    (rpt strip_tac >>
     `slots_in_range (get_storage cx st b)
        (off + 1 + j * type_slot_size tv) tv` by
       (Cases_on `j = len` >- gvs[] >>
        irule dyn_slots_in_range_index >> qexists `len` >>
        qpat_x_assum
          `slots_in_range _ off (ArrayTV tv (Dynamic max))` mp_tac >>
        simp[slots_in_range_def] >> decide_tac) >>
     `j < max` by decide_tac >>
     `j * type_slot_size tv + type_slot_size tv <=
      max * type_slot_size tv` by
       (irule array_index_element_end_bound >> simp[]) >>
     `off + 1 + j * type_slot_size tv + type_slot_size tv <=
      dimword(:256)` by
       (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
     `off + 1 + j * type_slot_size tv < dimword(:256)` by decide_tac >>
     drule typed_write_storage_slot_preserves_disjoint_num_region >>
     disch_then drule >> disch_then drule >>
     disch_then drule >> disch_then irule >>
     simp[vyperValueTheory.type_slot_size_def] >>
     rewrite_tac[ranges_disjoint_def] >> decide_tac) >>
  simp[slots_in_range_def] >>
  `w2n (n2w (len + 1) : bytes32) = len + 1` by simp[] >>
  gvs[arithmeticTheory.MIN_DEF] >>
  irule dyn_slots_in_range_reconstruct >> simp[]
QED



Theorem dynamic_array_append_two_writes_preserve_v2:
  slots_in_range (get_storage cx st b) off (ArrayTV tv (Dynamic max)) /\
  w2n (read_slot (get_storage cx st b) off) = len /\
  len < max /\
  max < dimword(:256) /\
  0 < type_slot_size tv /\
  well_formed_type_value tv /\
  off + type_slot_size (ArrayTV tv (Dynamic max)) <= dimword(:256) /\
  value_has_type tv v /\
  write_storage_slot cx b
    (n2w (off + 1 + len * type_slot_size tv)) tv v st = (INL (), st1) /\
  write_storage_slot cx b (n2w off) (BaseTV (UintT 256))
    (IntV (&(len + 1))) st1 = (INL (), st2) ==>
  slots_in_range (get_storage cx st2 b) off (ArrayTV tv (Dynamic max))
Proof
  rpt gen_tac >> strip_tac >>
  `slots_in_range (get_storage cx st1 b) off
       (ArrayTV tv (Dynamic max)) /\
   slots_in_range (get_storage cx st1 b)
       (off + 1 + len * type_slot_size tv) tv /\
   read_slot (get_storage cx st1 b) off =
       read_slot (get_storage cx st b) off` by
    (irule dynamic_array_append_element_write_prefix >> simp[] >>
     qexists `v` >> simp[] >>
     `n2w (off + (len * type_slot_size tv + 1)) : bytes32 =
      n2w (off + 1 + len * type_slot_size tv)` by
       (AP_TERM_TAC >> decide_tac) >>
     pop_assum (fn th => once_rewrite_tac [th]) >>
     first_assum ACCEPT_TAC) >>
  `len + 1 <= max` by decide_tac >>
  `len + 1 < dimword(:256)` by decide_tac >>
  `value_has_type (BaseTV (UintT 256)) (IntV (&(len + 1)))` by
    (simp[value_has_type_def, integerTheory.NUM_OF_INT,
          integerTheory.INT_POS] >>
     qpat_x_assum `len + 1 < dimword(:256)` mp_tac >> simp[]) >>
  qpat_x_assum
    `write_storage_slot cx b (n2w off) (BaseTV (UintT 256)) _ st1 = _`
    mp_tac >>
  qpat_x_assum
    `read_slot (get_storage cx st1 b) off = _`
    mp_tac >>
  simp[] >> rpt strip_tac >>
  drule_at (Pat `write_storage_slot`)
    dynamic_array_append_header_write_reconstruct_forward >>
  disch_then (qspecl_then [`tv`, `max`] irule) >>
  simp[] >>
  qpat_x_assum
    `slots_in_range (get_storage cx st1 b)
       (off + 1 + len * type_slot_size tv) tv` mp_tac >>
  AP_TERM_TAC >> AP_TERM_TAC >> decide_tac
QED

Theorem resolve_array_element_dynamic_append_element_write_preserves_root:
  !cx b base tv subs st slot elem_tv max st_res len v st1 tenv ty.
    evaluate_type tenv ty = SOME tv /\
    well_formed_type_value tv /\
    well_formed_type_value elem_tv /\
    0 < type_slot_size elem_tv /\
    w2n (base:bytes32) + type_slot_size tv <= dimword(:256) /\
    slots_in_range (get_storage cx st b) (w2n base) tv /\
    resolve_array_element cx b base tv subs st =
      (INL (slot, ArrayTV elem_tv (Dynamic max), []), st_res) /\
    w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max)) <=
      dimword(:256) /\
    slots_in_range (get_storage cx st_res b) (w2n slot)
      (ArrayTV elem_tv (Dynamic max)) /\
    w2n (read_slot (get_storage cx st_res b) (w2n slot)) = len /\
    len < max /\
    value_has_type elem_tv v /\
    write_storage_slot cx b
      (n2w (w2n slot + 1 + len * type_slot_size elem_tv))
      elem_tv v st_res = (INL (), st1) ==>
    slots_in_range (get_storage cx st1 b) (w2n base) tv
Proof
  rpt strip_tac >>
  `n2w (w2n slot + (len * type_slot_size elem_tv + 1)) : bytes32 =
   n2w (w2n slot + 1 + len * type_slot_size elem_tv)` by
    (AP_TERM_TAC >> decide_tac) >>
  `slots_in_range (get_storage cx st1 b) (w2n slot)
       (ArrayTV elem_tv (Dynamic max)) /\
   slots_in_range (get_storage cx st1 b)
       (w2n slot + 1 + len * type_slot_size elem_tv) elem_tv /\
   read_slot (get_storage cx st1 b) (w2n slot) =
       read_slot (get_storage cx st_res b) (w2n slot)` by
    (irule dynamic_array_append_element_write_prefix >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac
     >- (qexists `v` >>
         conj_tac
         >- (qpat_x_assum
               `write_storage_slot cx b
                  (n2w (w2n slot + 1 + len * type_slot_size elem_tv)) _ _ _ = _`
               mp_tac >>
             qpat_assum
               `n2w (w2n slot + (len * type_slot_size elem_tv + 1)) = _`
               (fn th => once_rewrite_tac [th]) >> simp[]) >>
         first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  `len * type_slot_size elem_tv + type_slot_size elem_tv <=
   max * type_slot_size elem_tv` by
    (irule array_index_element_end_bound >> simp[]) >>
  `w2n slot + 1 + len * type_slot_size elem_tv < dimword(:256)` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `w2n (n2w (w2n slot + 1 + len * type_slot_size elem_tv) : bytes32) =
   w2n slot + 1 + len * type_slot_size elem_tv` by simp[] >>
  `w2n slot <=
   w2n (n2w (w2n slot + 1 + len * type_slot_size elem_tv) : bytes32)` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `w2n (n2w (w2n slot + 1 + len * type_slot_size elem_tv) : bytes32) +
     type_slot_size elem_tv <=
   w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max))` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  irule resolve_array_element_contained_write_preserves_root >>
  simp[] >>
  conj_tac
  >- (qexistsl [`tenv`, `ty`] >> simp[]) >>
  qexistsl [`ArrayTV elem_tv (Dynamic max)`, `slot`, `st`, `st_res`, `subs`,
             `n2w (w2n slot + 1 + len * type_slot_size elem_tv)`,
             `elem_tv`, `v`] >>
  simp[]
QED

Theorem resolve_array_element_dynamic_append_two_writes_preserve_root:
  !cx b base tv subs st slot elem_tv max st_res len v st1 st2 tenv ty.
    evaluate_type tenv ty = SOME tv /\
    well_formed_type_value tv /\
    well_formed_type_value elem_tv /\
    0 < type_slot_size elem_tv /\
    w2n (base:bytes32) + type_slot_size tv <= dimword(:256) /\
    slots_in_range (get_storage cx st b) (w2n base) tv /\
    resolve_array_element cx b base tv subs st =
      (INL (slot, ArrayTV elem_tv (Dynamic max), []), st_res) /\
    w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max)) <=
      dimword(:256) /\
    slots_in_range (get_storage cx st_res b) (w2n slot)
      (ArrayTV elem_tv (Dynamic max)) /\
    w2n (read_slot (get_storage cx st_res b) (w2n slot)) = len /\
    len < max /\
    max < dimword(:256) /\
    value_has_type elem_tv v /\
    write_storage_slot cx b
      (n2w (w2n slot + 1 + len * type_slot_size elem_tv))
      elem_tv v st_res = (INL (), st1) /\
    write_storage_slot cx b (n2w (w2n slot)) (BaseTV (UintT 256))
      (IntV (&(len + 1))) st1 = (INL (), st2) ==>
    slots_in_range (get_storage cx st2 b) (w2n base) tv
Proof
  rpt strip_tac >>
  `n2w (w2n slot + (len * type_slot_size elem_tv + 1)) : bytes32 =
   n2w (w2n slot + 1 + len * type_slot_size elem_tv)` by
    (AP_TERM_TAC >> decide_tac) >>
  `slots_in_range (get_storage cx st2 b) (w2n slot)
     (ArrayTV elem_tv (Dynamic max))` by
    (irule dynamic_array_append_two_writes_preserve_v2 >> simp[] >>
     qexistsl [`st_res`, `st1`, `v`] >>
     conj_tac
     >- (qpat_assum
           `w2n (read_slot (get_storage cx st_res b) (w2n slot)) = len`
           (fn th => rewrite_tac [th]) >>
         simp[] >>
         first_assum ACCEPT_TAC) >>
     conj_tac
     >- (`n2w (w2n slot) : bytes32 = slot` by simp[] >>
         qpat_assum `n2w (w2n slot) : bytes32 = slot`
           (fn th => once_rewrite_tac [GSYM th]) >>
         `w2n (n2w (w2n slot) : bytes32) = w2n slot` by simp[] >>
         qpat_assum `w2n (n2w (w2n slot) : bytes32) = w2n slot`
           (fn th => once_rewrite_tac [th]) >>
         qpat_assum
           `w2n (read_slot (get_storage cx st_res b) (w2n slot)) = len`
           (fn th => rewrite_tac [th]) >>
         first_assum ACCEPT_TAC) >>
     conj_tac
     >- (qpat_assum
           `w2n (read_slot (get_storage cx st_res b) (w2n slot)) = len`
           (fn th => rewrite_tac [th]) >>
         `n2w (w2n slot + (type_slot_size elem_tv * len + 1)) : bytes32 =
          n2w (w2n slot + 1 + len * type_slot_size elem_tv)` by
           (AP_TERM_TAC >> decide_tac) >>
         qpat_assum
           `n2w (w2n slot + (type_slot_size elem_tv * len + 1)) : bytes32 = _`
           (fn th => once_rewrite_tac [th]) >>
         first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     first_assum ACCEPT_TAC) >>
  `len + 1 < dimword(:256)` by decide_tac >>
  `value_has_type (BaseTV (UintT 256)) (IntV (&(len + 1)))` by
    (simp[value_has_type_def, integerTheory.NUM_OF_INT,
          integerTheory.INT_POS] >>
     qpat_x_assum `len + 1 < dimword(:256)` mp_tac >> simp[]) >>
  `len * type_slot_size elem_tv + type_slot_size elem_tv <=
   max * type_slot_size elem_tv` by
    (irule array_index_element_end_bound >> simp[]) >>
  `w2n slot + 1 + len * type_slot_size elem_tv < dimword(:256)` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `w2n (n2w (w2n slot + 1 + len * type_slot_size elem_tv) : bytes32) =
   w2n slot + 1 + len * type_slot_size elem_tv` by simp[] >>
  `w2n slot <=
   w2n (n2w (w2n slot + 1 + len * type_slot_size elem_tv) : bytes32)` by
    decide_tac >>
  `w2n (n2w (w2n slot + 1 + len * type_slot_size elem_tv) : bytes32) +
     type_slot_size elem_tv <=
   w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max))` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `w2n slot <= w2n (n2w (w2n slot) : bytes32)` by
    simp[wordsTheory.w2n_lt] >>
  `w2n (n2w (w2n slot) : bytes32) +
     type_slot_size (BaseTV (UintT 256)) <=
   w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max))` by
    simp[vyperValueTheory.type_slot_size_def, wordsTheory.w2n_lt] >>
  irule resolve_array_element_two_contained_writes_preserve_root >>
  simp[] >>
  conj_tac
  >- (qexistsl [`tenv`, `ty`] >> simp[]) >>
  qexistsl [`ArrayTV elem_tv (Dynamic max)`, `slot`, `st`, `st1`, `st_res`,
             `subs`,
             `n2w (w2n slot + 1 + len * type_slot_size elem_tv)`,
             `n2w (w2n slot)`, `elem_tv`, `BaseTV (UintT 256)`,
             `v`, `IntV (&(len + 1))`] >>
  simp[wordsTheory.w2n_lt] >>
  decide_tac
QED



Theorem dynamic_array_pop_element_write_prefix[local]:
  slots_in_range (get_storage cx st b) off (ArrayTV tv (Dynamic max)) /\
  w2n (read_slot (get_storage cx st b) off) = len /\
  0 < len /\
  0 < type_slot_size tv /\
  well_formed_type_value tv /\
  off + type_slot_size (ArrayTV tv (Dynamic max)) <= dimword(:256) /\
  value_has_type tv v /\
  write_storage_slot cx b
    (n2w (off + 1 + (len - 1) * type_slot_size tv)) tv v st =
      (INL (), st') ==>
  slots_in_range (get_storage cx st' b) off (ArrayTV tv (Dynamic max)) /\
  read_slot (get_storage cx st' b) off =
    read_slot (get_storage cx st b) off
Proof
  rpt gen_tac >> strip_tac >>
  `len <= max` by
    (qpat_x_assum `slots_in_range _ off (ArrayTV tv (Dynamic max))` mp_tac >>
     simp[slots_in_range_def]) >>
  `len - 1 < max` by decide_tac >>
  `(len - 1) * type_slot_size tv + type_slot_size tv <=
   max * type_slot_size tv` by
    (irule array_index_element_end_bound >> simp[]) >>
  `off + 1 + (len - 1) * type_slot_size tv + type_slot_size tv <=
   dimword(:256)` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `off + 1 + (len - 1) * type_slot_size tv < dimword(:256)` by decide_tac >>
  `w2n (n2w (off + 1 + (len - 1) * type_slot_size tv) : bytes32) =
   off + 1 + (len - 1) * type_slot_size tv` by simp[] >>
  `slots_in_range (get_storage cx st' b)
     (off + 1 + (len - 1) * type_slot_size tv) tv` by
    (drule typed_write_storage_slot_establishes_region_forward >> simp[]) >>
  conj_tac
  >- (drule dynamic_array_typed_leaf_write_reconstruct_curried >>
      disch_then irule >> simp[] >>
      qexistsl [`tv`, `len - 1`,
        `n2w (off + 1 + (len - 1) * type_slot_size tv)`, `v`] >>
      simp[] >>
      `off + (type_slot_size tv * (len - 1) + 1) =
       off + 1 + (len - 1) * type_slot_size tv` by
        (once_rewrite_tac [arithmeticTheory.MULT_COMM] >> decide_tac) >>
      pop_assum (fn th => once_rewrite_tac [th]) >>
      first_assum ACCEPT_TAC) >>
  drule typed_write_storage_slot_preserves_disjoint_read_slot >>
  disch_then drule >> disch_then irule >>
  qpat_assum
    `w2n (n2w (off + 1 + (len - 1) * type_slot_size tv) : bytes32) = _`
    (fn th => rewrite_tac [th]) >>
  rewrite_tac[ranges_disjoint_def] >>
  decide_tac
QED

Theorem dynamic_array_shrink_header_write_reconstruct_forward[local]:
  write_storage_slot cx b (n2w off) (BaseTV (UintT 256))
    (IntV (&new_len)) st = (INL (), st') ==>
  slots_in_range (get_storage cx st b) off (ArrayTV tv (Dynamic max)) ==>
  w2n (read_slot (get_storage cx st b) off) = old_len ==>
  new_len <= old_len ==>
  old_len <= max ==>
  0 < type_slot_size tv ==>
  off + type_slot_size (ArrayTV tv (Dynamic max)) <= dimword(:256) ==>
  value_has_type (BaseTV (UintT 256)) (IntV (&new_len)) ==>
  slots_in_range (get_storage cx st' b) off (ArrayTV tv (Dynamic max))
Proof
  rpt strip_tac >>
  `new_len <= max` by decide_tac >>
  `new_len < dimword(:256)` by
    (qpat_x_assum `value_has_type _ _` mp_tac >>
     simp[value_has_type_def, integerTheory.NUM_OF_INT,
          integerTheory.INT_POS]) >>
  `off < dimword(:256)` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `w2n (n2w off : bytes32) = off` by simp[] >>
  `MIN old_len max = old_len` by
    (simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  `dyn_slots_in_range (get_storage cx st b) (off + 1) tv old_len` by
    (qpat_x_assum `slots_in_range _ off (ArrayTV tv (Dynamic max))` mp_tac >>
     simp[slots_in_range_def]) >>
  `read_slot (get_storage cx st' b) off = n2w new_len` by
    (drule_at (Pat `write_storage_slot`) uint256_header_write_read_exact >>
     simp[]) >>
  `!j. j < new_len ==>
       slots_in_range (get_storage cx st' b)
         (off + 1 + j * type_slot_size tv) tv` by
    (rpt strip_tac >>
     `slots_in_range (get_storage cx st b)
        (off + 1 + j * type_slot_size tv) tv` by
       (irule dyn_slots_in_range_index >> qexists `old_len` >> simp[]) >>
     `j < max` by decide_tac >>
     `j * type_slot_size tv + type_slot_size tv <=
      max * type_slot_size tv` by
       (irule array_index_element_end_bound >> simp[]) >>
     `off + 1 + j * type_slot_size tv + type_slot_size tv <=
      dimword(:256)` by
       (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
     `off + 1 + j * type_slot_size tv < dimword(:256)` by decide_tac >>
     drule typed_write_storage_slot_preserves_disjoint_num_region >>
     disch_then drule >> disch_then drule >>
     disch_then drule >> disch_then irule >>
     simp[vyperValueTheory.type_slot_size_def] >>
     rewrite_tac[ranges_disjoint_def] >> decide_tac) >>
  simp[slots_in_range_def] >>
  `w2n (n2w new_len : bytes32) = new_len` by simp[] >>
  gvs[arithmeticTheory.MIN_DEF] >>
  irule dyn_slots_in_range_reconstruct >> simp[]
QED




Theorem dynamic_array_pop_two_writes_preserve:
  slots_in_range (get_storage cx st b) off (ArrayTV tv (Dynamic max)) /\
  w2n (read_slot (get_storage cx st b) off) = len /\
  0 < len /\
  0 < type_slot_size tv /\
  well_formed_type_value tv /\
  off + type_slot_size (ArrayTV tv (Dynamic max)) <= dimword(:256) /\
  value_has_type tv default /\
  write_storage_slot cx b
    (n2w (off + 1 + (len - 1) * type_slot_size tv)) tv default st =
      (INL (), st1) /\
  write_storage_slot cx b (n2w off) (BaseTV (UintT 256))
    (IntV (&(len - 1))) st1 = (INL (), st2) ==>
  slots_in_range (get_storage cx st2 b) off (ArrayTV tv (Dynamic max))
Proof
  rpt gen_tac >> strip_tac >>
  `slots_in_range (get_storage cx st1 b) off
       (ArrayTV tv (Dynamic max)) /\
   read_slot (get_storage cx st1 b) off =
       read_slot (get_storage cx st b) off` by
    (irule dynamic_array_pop_element_write_prefix >> simp[] >>
     qexists `default` >> simp[] >>
     `n2w (off + (type_slot_size tv * (len - 1) + 1)) : bytes32 =
      n2w (off + 1 + (len - 1) * type_slot_size tv)` by
       (AP_TERM_TAC >>
        once_rewrite_tac [arithmeticTheory.MULT_COMM] >> decide_tac) >>
     pop_assum (fn th => once_rewrite_tac [th]) >>
     first_assum ACCEPT_TAC) >>
  `len <= max` by
    (qpat_x_assum `slots_in_range _ off (ArrayTV tv (Dynamic max))` mp_tac >>
     simp[slots_in_range_def]) >>
  `len < dimword(:256)` by
    (qpat_x_assum `w2n (read_slot _ off) = len` (fn th => once_rewrite_tac [GSYM th]) >>
     MATCH_ACCEPT_TAC wordsTheory.w2n_lt) >>
  `len - 1 < dimword(:256)` by decide_tac >>
  `value_has_type (BaseTV (UintT 256)) (IntV (&(len - 1)))` by
    (simp[value_has_type_def, integerTheory.NUM_OF_INT,
          integerTheory.INT_POS] >>
     qpat_x_assum `len - 1 < dimword(:256)` mp_tac >> simp[]) >>
  qpat_x_assum
    `write_storage_slot cx b (n2w off) (BaseTV (UintT 256)) _ st1 = _`
    mp_tac >>
  qpat_x_assum
    `read_slot (get_storage cx st1 b) off = _`
    mp_tac >>
  simp[] >> rpt strip_tac >>
  drule_at (Pat `write_storage_slot`)
    dynamic_array_shrink_header_write_reconstruct_forward >>
  disch_then (qspecl_then [`tv`, `max`] irule) >>
  simp[]
QED

Theorem resolve_array_element_dynamic_pop_element_write_preserves_root:
  !cx b base tv subs st slot elem_tv max st_res len v st1 tenv ty.
    evaluate_type tenv ty = SOME tv /\
    well_formed_type_value tv /\
    well_formed_type_value elem_tv /\
    0 < type_slot_size elem_tv /\
    w2n (base:bytes32) + type_slot_size tv <= dimword(:256) /\
    slots_in_range (get_storage cx st b) (w2n base) tv /\
    resolve_array_element cx b base tv subs st =
      (INL (slot, ArrayTV elem_tv (Dynamic max), []), st_res) /\
    w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max)) <=
      dimword(:256) /\
    slots_in_range (get_storage cx st_res b) (w2n slot)
      (ArrayTV elem_tv (Dynamic max)) /\
    w2n (read_slot (get_storage cx st_res b) (w2n slot)) = len /\
    0 < len /\
    value_has_type elem_tv v /\
    write_storage_slot cx b
      (n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv))
      elem_tv v st_res = (INL (), st1) ==>
    slots_in_range (get_storage cx st1 b) (w2n base) tv
Proof
  rpt strip_tac >>
  `slots_in_range (get_storage cx st1 b) (w2n slot)
       (ArrayTV elem_tv (Dynamic max)) /\
   read_slot (get_storage cx st1 b) (w2n slot) =
       read_slot (get_storage cx st_res b) (w2n slot)` by
    (irule dynamic_array_pop_element_write_prefix >> simp[] >>
     qexists `v` >> simp[] >>
     `n2w (w2n slot + (type_slot_size elem_tv * (len - 1) + 1)) : bytes32 =
      n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv)` by
       (AP_TERM_TAC >>
        once_rewrite_tac [arithmeticTheory.MULT_COMM] >> decide_tac) >>
     pop_assum (fn th => once_rewrite_tac [th]) >>
     first_assum ACCEPT_TAC) >>
  `len <= max` by
    (qpat_x_assum
       `slots_in_range _ (w2n slot) (ArrayTV elem_tv (Dynamic max))` mp_tac >>
     simp[slots_in_range_def]) >>
  `(len - 1) * type_slot_size elem_tv + type_slot_size elem_tv <=
   max * type_slot_size elem_tv` by
    (irule array_index_element_end_bound >> decide_tac) >>
  `w2n slot + 1 + (len - 1) * type_slot_size elem_tv < dimword(:256)` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `w2n (n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv) : bytes32) =
   w2n slot + 1 + (len - 1) * type_slot_size elem_tv` by simp[] >>
  `w2n slot <=
   w2n (n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv) : bytes32)` by
    decide_tac >>
  `w2n (n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv) : bytes32) +
     type_slot_size elem_tv <=
   w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max))` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  irule resolve_array_element_contained_write_preserves_root >>
  simp[] >>
  conj_tac
  >- (qexistsl [`tenv`, `ty`] >> simp[]) >>
  qexistsl [`ArrayTV elem_tv (Dynamic max)`, `slot`, `st`, `st_res`, `subs`,
             `n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv)`,
             `elem_tv`, `v`] >>
  simp[]
QED


Theorem resolve_array_element_dynamic_pop_two_writes_preserve_root:
  !cx b base tv subs st slot elem_tv max st_res len v st1 st2 tenv ty.
    evaluate_type tenv ty = SOME tv /\
    well_formed_type_value tv /\
    well_formed_type_value elem_tv /\
    0 < type_slot_size elem_tv /\
    w2n (base:bytes32) + type_slot_size tv <= dimword(:256) /\
    slots_in_range (get_storage cx st b) (w2n base) tv /\
    resolve_array_element cx b base tv subs st =
      (INL (slot, ArrayTV elem_tv (Dynamic max), []), st_res) /\
    w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max)) <=
      dimword(:256) /\
    slots_in_range (get_storage cx st_res b) (w2n slot)
      (ArrayTV elem_tv (Dynamic max)) /\
    w2n (read_slot (get_storage cx st_res b) (w2n slot)) = len /\
    0 < len /\
    value_has_type elem_tv v /\
    write_storage_slot cx b
      (n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv))
      elem_tv v st_res = (INL (), st1) /\
    write_storage_slot cx b (n2w (w2n slot)) (BaseTV (UintT 256))
      (IntV (&(len - 1))) st1 = (INL (), st2) ==>
    slots_in_range (get_storage cx st2 b) (w2n base) tv
Proof
  rpt strip_tac >>
  `slots_in_range (get_storage cx st2 b) (w2n slot)
     (ArrayTV elem_tv (Dynamic max))` by
    (irule dynamic_array_pop_two_writes_preserve >> simp[] >>
     qexistsl [`v`, `st_res`, `st1`] >> simp[] >>
     `n2w (w2n slot + (type_slot_size elem_tv * (len - 1) + 1)) : bytes32 =
      n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv)` by
       (AP_TERM_TAC >>
        once_rewrite_tac [arithmeticTheory.MULT_COMM] >> decide_tac) >>
     pop_assum (fn th => once_rewrite_tac [th]) >>
     `n2w (w2n slot) : bytes32 = slot` by simp[] >>
     qpat_assum `n2w (w2n slot) : bytes32 = slot`
       (fn th => once_rewrite_tac [GSYM th]) >>
     `w2n (n2w (w2n slot) : bytes32) = w2n slot` by simp[] >>
     qpat_assum `w2n (n2w (w2n slot) : bytes32) = w2n slot`
       (fn th => once_rewrite_tac [th]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     first_assum ACCEPT_TAC) >>
  `len <= max` by
    (qpat_x_assum
       `slots_in_range (get_storage cx st_res b) (w2n slot)
          (ArrayTV elem_tv (Dynamic max))` mp_tac >>
     simp[slots_in_range_def]) >>
  `len < dimword(:256)` by
    (qpat_x_assum `w2n (read_slot _ (w2n slot)) = len`
       (fn th => once_rewrite_tac [GSYM th]) >>
     MATCH_ACCEPT_TAC wordsTheory.w2n_lt) >>
  `len - 1 < dimword(:256)` by decide_tac >>
  `value_has_type (BaseTV (UintT 256)) (IntV (&(len - 1)))` by
    (simp[value_has_type_def, integerTheory.NUM_OF_INT,
          integerTheory.INT_POS] >>
     qpat_x_assum `len - 1 < dimword(:256)` mp_tac >> simp[]) >>
  `(len - 1) * type_slot_size elem_tv + type_slot_size elem_tv <=
   max * type_slot_size elem_tv` by
    (irule array_index_element_end_bound >> decide_tac) >>
  `w2n slot + 1 + (len - 1) * type_slot_size elem_tv < dimword(:256)` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `w2n (n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv) : bytes32) =
   w2n slot + 1 + (len - 1) * type_slot_size elem_tv` by simp[] >>
  `w2n slot <=
   w2n (n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv) : bytes32)` by
    decide_tac >>
  `w2n (n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv) : bytes32) +
     type_slot_size elem_tv <=
   w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max))` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `w2n slot <= w2n (n2w (w2n slot) : bytes32)` by
    simp[wordsTheory.w2n_lt] >>
  `w2n (n2w (w2n slot) : bytes32) +
     type_slot_size (BaseTV (UintT 256)) <=
   w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max))` by
    simp[vyperValueTheory.type_slot_size_def, wordsTheory.w2n_lt] >>
  irule resolve_array_element_two_contained_writes_preserve_root >>
  simp[] >>
  conj_tac
  >- (qexistsl [`tenv`, `ty`] >> simp[]) >>
  qexistsl [`ArrayTV elem_tv (Dynamic max)`, `slot`, `st`, `st1`, `st_res`,
             `subs`,
             `n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv)`,
             `n2w (w2n slot)`, `elem_tv`, `BaseTV (UintT 256)`,
             `v`, `IntV (&(len - 1))`] >>
  simp[wordsTheory.w2n_lt] >>
  decide_tac
QED

Theorem zero_slot_size_slots_in_range[local]:
  (!tv storage off.
     type_slot_size tv = 0 ==> slots_in_range storage off tv) /\
  (!fields storage off.
     type_slot_size_fields fields = 0 ==>
     struct_slots_in_range storage off fields) /\
  (!(p:string # type_value) storage off.
     type_slot_size (SND p) = 0 ==>
     slots_in_range storage off (SND p)) /\

  (!tvs storage off.
     type_slot_size_list tvs = 0 ==>
     tuple_slots_in_range storage off tvs)
Proof
  ho_match_mp_tac (TypeBase.induction_of ``:type_value``) >>
  simp[vyperValueTheory.type_slot_size_def, slots_in_range_def] >>
  rpt conj_tac >> rpt strip_tac >> simp[] >>
  TRY (rename1 `slots_in_range storage off (BaseTV b)` >>
       Cases_on `b` >>
       simp[vyperValueTheory.type_slot_size_def, slots_in_range_def]) >>
  TRY (rename1 `slots_in_range storage off (BaseTV (BytesT bd))` >>
       Cases_on `bd` >>
       simp[vyperValueTheory.type_slot_size_def, slots_in_range_def]) >>
  TRY (rename1 `slots_in_range storage off (ArrayTV elem bd)` >>
       Cases_on `bd` >>
       gvs[vyperValueTheory.type_slot_size_def, slots_in_range_def] >>
       Induct_on `n` >> simp[slots_in_range_def]) >>
  TRY (qpat_x_assum
         `type_slot_size (BaseTV (StringT n)) = 0` mp_tac >>
       simp[vyperValueTheory.type_slot_size_def]) >>
  TRY (qpat_x_assum
         `type_slot_size (BaseTV (BytesT (Dynamic n))) = 0` mp_tac >>
       simp[vyperValueTheory.type_slot_size_def]) >>
  TRY (rename1 `struct_slots_in_range storage off (p::fields)` >>
       PairCases_on `p` >>
       gvs[vyperValueTheory.type_slot_size_def, slots_in_range_def] >>
       metis_tac[]) >>
  metis_tac[]
QED


Theorem resolved_write_contained_in_declared_root[local]:
  evaluate_type tenv ty = SOME tv /\
  w2n (root_slot:bytes32) + type_slot_size tv <= dimword(:256) /\
  resolve_array_element cx b root_slot tv subs st =
    (INL (slot,selected_tv,rsubs),st_res) /\
  w2n slot <= w2n wr_slot /\
  w2n wr_slot + type_slot_size wr_tv <=
    w2n slot + type_slot_size selected_tv ==>
  w2n root_slot <= w2n wr_slot /\
  w2n wr_slot + type_slot_size wr_tv <=
    w2n root_slot + type_slot_size tv
Proof
  rpt strip_tac >>
  drule_at (Pat `resolve_array_element`) resolve_array_element_region_bounds >>
  disch_then (qspecl_then [`tenv`, `ty`] mp_tac) >>
  simp[] >> decide_tac
QED


(* Contract-level framing for one concrete typed write contained in an
   ordinary declared root.  The caller supplies reconstruction of that root;
   layout separation frames every distinct semantic declaration. *)
Theorem contained_ordinary_write_preserves_contract_storage_well_formed:
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  declared_storage_region cx mid n [] = SOME (b,root_slot,tv) /\
  value_has_type wr_tv wr_v /\
  write_storage_slot cx b wr_slot wr_tv wr_v st = (INL (),st') /\
  w2n root_slot <= w2n wr_slot /\
  w2n wr_slot + type_slot_size wr_tv <=
    w2n root_slot + type_slot_size tv /\
  slots_in_range (get_storage cx st' b) (w2n root_slot) tv ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  `!mid' n' subs' b' slot' tv' storage st''.
     declared_storage_region cx mid' n' subs' = SOME (b',slot',tv') /\
     get_storage_backend cx b' st' = (INL storage,st'') ==>
     slots_in_range storage (w2n slot') tv'` by
    (rpt gen_tac >> strip_tac >>
     gvs[vyperStorageBackendTheory.get_storage_backend_eq] >>
     Cases_on `(mid,n,[]) = (mid',n',subs')`
     >- (gvs[]) >>
     `slots_in_range (get_storage cx st b') (w2n slot') tv'` by
       (qpat_x_assum `contract_storage_well_formed cx st` mp_tac >>
        simp[contract_storage_well_formed_def,
             vyperStorageBackendTheory.get_storage_backend_eq] >>
        metis_tac[]) >>
     `b <> b' \/
      ranges_disjoint (w2n wr_slot) (type_slot_size wr_tv)
                      (w2n slot') (type_slot_size tv')` by
       (Cases_on `b = b'` >- (gvs[] >>
        `ranges_disjoint (w2n root_slot) (type_slot_size tv)
                         (w2n slot') (type_slot_size tv')` by
          (qpat_x_assum `storage_layout_safe cx` mp_tac >>
           simp[storage_layout_safe_def] >> strip_tac >>
           qpat_x_assum
             `!mid1 n1 subs1 mid2 n2 subs2 bb slot1 tv1 slot2 tv2. _`
             (qspecl_then
                [`mid`, `n`, `[]`, `mid'`, `n'`, `subs'`, `b`,
                 `root_slot`, `tv`, `slot'`, `tv'`] mp_tac) >>
           (impl_tac >- simp[]) >>
           strip_tac >- gvs[] >> simp[]) >>
        gvs[ranges_disjoint_def] >> decide_tac) >>
        simp[]) >>
     irule typed_write_storage_slot_preserves_disjoint_region >>
     simp[] >>
     qexistsl [`b`, `wr_slot`, `st`, `wr_tv`, `wr_v`] >> simp[]) >>
  simp[contract_storage_well_formed_def] >>
  conj_tac
  >- (simp[well_formed_storage_def, storage_var_in_range_def] >>
      rpt gen_tac >> strip_tac >>
      `declared_storage_region cx mid' n' [] =
         SOME (is_transient,n2w off,tv')` by
        (irule declared_storage_region_ordinary >> simp[]) >>
      Cases_on `off < dimword(:256)`
      >- (qpat_assum
            `!m name subs bb sl ty stor s. _`
            (qspecl_then
               [`mid'`, `n'`, `[]`, `is_transient`, `n2w off`, `tv'`,
                `storage`, `st''`] mp_tac) >>
          simp[vyperStorageBackendTheory.get_storage_backend_eq,
               wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
      `off + type_slot_size tv' <= dimword(:256)` by
        (qpat_x_assum `storage_layout_safe cx` mp_tac >>
         simp[storage_layout_safe_def, well_formed_layout_def] >>
         metis_tac[]) >>
      `off = dimword(:256) /\ type_slot_size tv' = 0` by decide_tac >>
      irule (CONJUNCT1 zero_slot_size_slots_in_range) >> simp[]) >>
  metis_tac[]
QED
(* Sequential form for append/pop final endpoints.  The intermediate selected
   root fact is explicit because a failed second write may expose st1. *)
Theorem two_contained_ordinary_writes_preserve_contract_storage_well_formed:
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  declared_storage_region cx mid n [] = SOME (b,root_slot,tv) /\
  value_has_type wr_tv1 wr_v1 /\
  write_storage_slot cx b wr_slot1 wr_tv1 wr_v1 st = (INL (),st1) /\
  w2n root_slot <= w2n wr_slot1 /\
  w2n wr_slot1 + type_slot_size wr_tv1 <=
    w2n root_slot + type_slot_size tv /\
  slots_in_range (get_storage cx st1 b) (w2n root_slot) tv /\
  value_has_type wr_tv2 wr_v2 /\
  write_storage_slot cx b wr_slot2 wr_tv2 wr_v2 st1 = (INL (),st2) /\
  w2n root_slot <= w2n wr_slot2 /\
  w2n wr_slot2 + type_slot_size wr_tv2 <=
    w2n root_slot + type_slot_size tv /\
  slots_in_range (get_storage cx st2 b) (w2n root_slot) tv ==>
  contract_storage_well_formed cx st2
Proof
  metis_tac[contained_ordinary_write_preserves_contract_storage_well_formed]
QED



(* Contract endpoint after the element-initialisation write of dynamic append. *)
Theorem resolve_array_element_dynamic_append_element_write_preserves_contract_storage_well_formed:
  !cx mid n b root_slot tv subs st slot elem_tv max st_res len v st1 tenv ty.
    contract_storage_well_formed cx st /\
    storage_layout_safe cx /\
    declared_storage_region cx mid n [] = SOME (b,root_slot,tv) /\
    evaluate_type tenv ty = SOME tv /\
    well_formed_type_value tv /\
    well_formed_type_value elem_tv /\
    0 < type_slot_size elem_tv /\
    w2n (root_slot:bytes32) + type_slot_size tv <= dimword(:256) /\
    slots_in_range (get_storage cx st b) (w2n root_slot) tv /\
    resolve_array_element cx b root_slot tv subs st =
      (INL (slot, ArrayTV elem_tv (Dynamic max), []), st_res) /\
    w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max)) <=
      dimword(:256) /\
    slots_in_range (get_storage cx st_res b) (w2n slot)
      (ArrayTV elem_tv (Dynamic max)) /\
    w2n (read_slot (get_storage cx st_res b) (w2n slot)) = len /\
    len < max /\
    value_has_type elem_tv v /\
    write_storage_slot cx b
      (n2w (w2n slot + 1 + len * type_slot_size elem_tv))
      elem_tv v st_res = (INL (), st1) ==>
    contract_storage_well_formed cx st1
Proof
  rpt strip_tac >>
  `contract_storage_well_formed cx st_res` by
    (qspecl_then
       [`cx`, `b`, `root_slot`, `tv`, `subs`, `st`,
        `INL (slot,ArrayTV elem_tv (Dynamic max),[])`, `st_res`]
       match_mp_tac resolve_array_element_preserves_contract_storage_well_formed >>
     simp[]) >>
  qpat_assum
    `w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max)) <= _`
    (mk_asm "selected_bound") >>
  `len * type_slot_size elem_tv + type_slot_size elem_tv <=
   max * type_slot_size elem_tv` by
    (irule array_index_element_end_bound >> simp[]) >>
  `w2n slot + 1 + len * type_slot_size elem_tv < dimword(:256)` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `w2n (n2w (w2n slot + 1 + len * type_slot_size elem_tv) : bytes32) =
   w2n slot + 1 + len * type_slot_size elem_tv` by simp[] >>
  `w2n slot <=
     w2n (n2w (w2n slot + 1 + len * type_slot_size elem_tv) : bytes32) /\
   w2n (n2w (w2n slot + 1 + len * type_slot_size elem_tv) : bytes32) +
     type_slot_size elem_tv <=
   w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max))` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `w2n root_slot <=
     w2n (n2w (w2n slot + 1 + len * type_slot_size elem_tv) : bytes32) /\
   w2n (n2w (w2n slot + 1 + len * type_slot_size elem_tv) : bytes32) +
     type_slot_size elem_tv <= w2n root_slot + type_slot_size tv` by
    (irule resolved_write_contained_in_declared_root >> simp[] >>
     conj_tac >- (qexistsl [`tenv`, `ty`] >> simp[]) >>
     qexistsl [`b`, `cx`, `[]`, `ArrayTV elem_tv (Dynamic max)`, `slot`,
               `st`, `st_res`, `subs`] >> simp[]) >>
  `type_slot_size (ArrayTV elem_tv (Dynamic max)) + w2n slot <=
   dimword(:256)` by
    (once_rewrite_tac [arithmeticTheory.ADD_COMM] >>
     asm "selected_bound" ACCEPT_TAC) >>
  pop_assum $ mk_asm "selected_bound_comm" >>
  `slots_in_range (get_storage cx st1 b) (w2n root_slot) tv` by
    (irule resolve_array_element_dynamic_append_element_write_preserves_root >>
     simp[] >>
     conj_tac >- (qexistsl [`tenv`, `ty`] >> simp[]) >>
     qexistsl [`elem_tv`, `max`, `slot`, `st`, `st_res`, `subs`, `v`] >> simp[] >>
     conj_tac
     >- (asm "selected_bound_comm" mp_tac >> simp[]) >>
     `w2n slot + (len * type_slot_size elem_tv + 1) =
      w2n slot + 1 + len * type_slot_size elem_tv` by decide_tac >>
     pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  irule contained_ordinary_write_preserves_contract_storage_well_formed >>
  simp[] >>
  qexistsl [`b`, `mid`, `n`, `root_slot`, `st_res`, `tv`,
             `n2w (w2n slot + 1 + len * type_slot_size elem_tv)`,
             `elem_tv`, `v`] >> simp[]
QED

(* Contract endpoint after both writes of dynamic append. *)
Theorem resolve_array_element_dynamic_append_final_write_preserves_contract_storage_well_formed:
  !cx mid n b root_slot tv subs st slot elem_tv max st_res len v st1 st2 tenv ty.
    contract_storage_well_formed cx st /\
    storage_layout_safe cx /\
    declared_storage_region cx mid n [] = SOME (b,root_slot,tv) /\
    evaluate_type tenv ty = SOME tv /\
    well_formed_type_value tv /\
    well_formed_type_value elem_tv /\
    0 < type_slot_size elem_tv /\
    w2n (root_slot:bytes32) + type_slot_size tv <= dimword(:256) /\
    slots_in_range (get_storage cx st b) (w2n root_slot) tv /\
    resolve_array_element cx b root_slot tv subs st =
      (INL (slot, ArrayTV elem_tv (Dynamic max), []), st_res) /\
    w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max)) <=
      dimword(:256) /\
    slots_in_range (get_storage cx st_res b) (w2n slot)
      (ArrayTV elem_tv (Dynamic max)) /\
    w2n (read_slot (get_storage cx st_res b) (w2n slot)) = len /\
    len < max /\
    max < dimword(:256) /\
    value_has_type elem_tv v /\
    write_storage_slot cx b
      (n2w (w2n slot + 1 + len * type_slot_size elem_tv))
      elem_tv v st_res = (INL (), st1) /\
    write_storage_slot cx b (n2w (w2n slot)) (BaseTV (UintT 256))
      (IntV (&(len + 1))) st1 = (INL (), st2) ==>
    contract_storage_well_formed cx st2
Proof
  rpt gen_tac >> strip_tac >>
  `len * type_slot_size elem_tv + type_slot_size elem_tv <=
   max * type_slot_size elem_tv` by
    (irule array_index_element_end_bound >> simp[]) >>
  `w2n slot + 1 + len * type_slot_size elem_tv < dimword(:256)` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `w2n (n2w (w2n slot + 1 + len * type_slot_size elem_tv) : bytes32) =
   w2n slot + 1 + len * type_slot_size elem_tv` by simp[] >>
  `w2n slot <=
     w2n (n2w (w2n slot + 1 + len * type_slot_size elem_tv) : bytes32) /\
   w2n (n2w (w2n slot + 1 + len * type_slot_size elem_tv) : bytes32) +
     type_slot_size elem_tv <=
   w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max))` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `w2n root_slot <=
     w2n (n2w (w2n slot + 1 + len * type_slot_size elem_tv) : bytes32) /\
   w2n (n2w (w2n slot + 1 + len * type_slot_size elem_tv) : bytes32) +
     type_slot_size elem_tv <= w2n root_slot + type_slot_size tv` by
    (irule resolved_write_contained_in_declared_root >> simp[] >>
     conj_tac >- (qexistsl [`tenv`, `ty`] >> simp[]) >>
     qexistsl [`b`, `cx`, `[]`, `ArrayTV elem_tv (Dynamic max)`, `slot`,
               `st`, `st_res`, `subs`] >> simp[]) >>
  `type_slot_size (ArrayTV elem_tv (Dynamic max)) + w2n slot <=
   dimword(:256)` by
    (once_rewrite_tac [arithmeticTheory.ADD_COMM] >>
     qpat_assum
       `w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max)) <= _`
       ACCEPT_TAC) >>
  pop_assum $ mk_asm "selected_bound_comm_final" >>
  `slots_in_range (get_storage cx st1 b) (w2n root_slot) tv` by
    (irule resolve_array_element_dynamic_append_element_write_preserves_root >>
     simp[] >>
     conj_tac >- (qexistsl [`tenv`, `ty`] >> simp[]) >>
     qexistsl [`elem_tv`, `max`, `slot`, `st`, `st_res`, `subs`, `v`] >>
     simp[] >>
     conj_tac
     >- (asm "selected_bound_comm_final" mp_tac >> simp[]) >>
     `w2n slot + (len * type_slot_size elem_tv + 1) =
      w2n slot + 1 + len * type_slot_size elem_tv` by decide_tac >>
     pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `contract_storage_well_formed cx st1` by
    (drule_all
       resolve_array_element_dynamic_append_element_write_preserves_contract_storage_well_formed >>
     simp[]) >>
  `len + 1 < dimword(:256)` by decide_tac >>
  pop_assum $ mk_asm "len_succ_bound" >>
  `value_has_type (BaseTV (UintT 256)) (IntV (&(len + 1)))` by
    (simp[value_has_type_def, integerTheory.NUM_OF_INT,
          integerTheory.INT_POS] >>
     asm "len_succ_bound" mp_tac >> EVAL_TAC) >>
  `w2n root_slot <= w2n slot /\
   w2n slot + type_slot_size (BaseTV (UintT 256)) <=
   w2n root_slot + type_slot_size tv` by
    (irule resolved_write_contained_in_declared_root >> simp[] >>
     conj_tac >- (qexistsl [`tenv`, `ty`] >> simp[]) >>
     qexistsl [`b`, `cx`, `[]`, `ArrayTV elem_tv (Dynamic max)`, `slot`,
               `st`, `st_res`, `subs`] >>
     simp[vyperValueTheory.type_slot_size_def]) >>
  `n2w (w2n slot) : bytes32 = slot` by simp[] >>
  pop_assum $ mk_asm "header_slot_eq" >>
  `slots_in_range (get_storage cx st2 b) (w2n root_slot) tv` by
    (irule resolve_array_element_dynamic_append_two_writes_preserve_root >>
     simp[] >>
     conj_tac >- (qexistsl [`tenv`, `ty`] >> simp[]) >>
     qexistsl [`elem_tv`, `max`, `slot`, `st`, `st1`, `st_res`, `subs`, `v`] >>
     simp[] >>
     conj_tac
     >- (qpat_assum `max < dimword(:256)` mp_tac >> EVAL_TAC) >>
     conj_tac
     >- (asm "selected_bound_comm_final" mp_tac >> EVAL_TAC) >>
     conj_tac
     >- (asm "header_slot_eq" (fn th => once_rewrite_tac [GSYM th]) >>
         first_assum ACCEPT_TAC) >>
     `w2n slot + (len * type_slot_size elem_tv + 1) =
      w2n slot + 1 + len * type_slot_size elem_tv` by decide_tac >>
     pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  irule contained_ordinary_write_preserves_contract_storage_well_formed >>
  simp[] >>
  qexistsl [`b`, `mid`, `n`, `root_slot`, `st1`, `tv`,
             `slot`, `BaseTV (UintT 256)`,
             `IntV (&(len + 1))`] >> simp[] >>
  asm "header_slot_eq" (fn th => once_rewrite_tac [GSYM th]) >>
  first_assum ACCEPT_TAC
QED


(* Contract endpoint after the element-defaulting write of dynamic pop. *)
Theorem resolve_array_element_dynamic_pop_element_write_preserves_contract_storage_well_formed:
  !cx mid n b root_slot tv subs st slot elem_tv max st_res len v st1 tenv ty.
    contract_storage_well_formed cx st /\
    storage_layout_safe cx /\
    declared_storage_region cx mid n [] = SOME (b,root_slot,tv) /\
    evaluate_type tenv ty = SOME tv /\
    well_formed_type_value tv /\
    well_formed_type_value elem_tv /\
    0 < type_slot_size elem_tv /\
    w2n (root_slot:bytes32) + type_slot_size tv <= dimword(:256) /\
    slots_in_range (get_storage cx st b) (w2n root_slot) tv /\
    resolve_array_element cx b root_slot tv subs st =
      (INL (slot, ArrayTV elem_tv (Dynamic max), []), st_res) /\
    w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max)) <=
      dimword(:256) /\
    slots_in_range (get_storage cx st_res b) (w2n slot)
      (ArrayTV elem_tv (Dynamic max)) /\
    w2n (read_slot (get_storage cx st_res b) (w2n slot)) = len /\
    0 < len /\
    value_has_type elem_tv v /\
    write_storage_slot cx b
      (n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv))
      elem_tv v st_res = (INL (), st1) ==>
    contract_storage_well_formed cx st1
Proof
  rpt gen_tac >> strip_tac >>
  `contract_storage_well_formed cx st_res` by
    (qspecl_then
       [`cx`, `b`, `root_slot`, `tv`, `subs`, `st`,
        `INL (slot,ArrayTV elem_tv (Dynamic max),[])`, `st_res`]
       match_mp_tac resolve_array_element_preserves_contract_storage_well_formed >>
     simp[]) >>
  `len <= max` by
    (qpat_x_assum
       `slots_in_range _ (w2n slot) (ArrayTV elem_tv (Dynamic max))` mp_tac >>
     simp[slots_in_range_def]) >>
  `(len - 1) * type_slot_size elem_tv + type_slot_size elem_tv <=
   max * type_slot_size elem_tv` by
    (irule array_index_element_end_bound >> decide_tac) >>
  `w2n slot + 1 + (len - 1) * type_slot_size elem_tv < dimword(:256)` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `w2n (n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv) : bytes32) =
   w2n slot + 1 + (len - 1) * type_slot_size elem_tv` by simp[] >>
  `w2n slot <=
     w2n (n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv) : bytes32) /\
   w2n (n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv) : bytes32) +
     type_slot_size elem_tv <=
   w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max))` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `w2n root_slot <=
     w2n (n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv) : bytes32) /\
   w2n (n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv) : bytes32) +
     type_slot_size elem_tv <= w2n root_slot + type_slot_size tv` by
    (irule resolved_write_contained_in_declared_root >> simp[] >>
     conj_tac >- (qexistsl [`tenv`, `ty`] >> simp[]) >>
     qexistsl [`b`, `cx`, `[]`, `ArrayTV elem_tv (Dynamic max)`, `slot`,
               `st`, `st_res`, `subs`] >> simp[]) >>
  `type_slot_size (ArrayTV elem_tv (Dynamic max)) + w2n slot <=
   dimword(:256)` by
    (once_rewrite_tac [arithmeticTheory.ADD_COMM] >>
     qpat_assum
       `w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max)) <= _`
       ACCEPT_TAC) >>
  pop_assum $ mk_asm "pop_selected_bound_comm" >>
  `slots_in_range (get_storage cx st1 b) (w2n root_slot) tv` by
    (irule resolve_array_element_dynamic_pop_element_write_preserves_root >>
     simp[] >>
     conj_tac >- (qexistsl [`tenv`, `ty`] >> simp[]) >>
     qexistsl [`elem_tv`, `max`, `slot`, `st`, `st_res`, `subs`, `v`] >>
     simp[] >>
     conj_tac
     >- (asm "pop_selected_bound_comm" mp_tac >> EVAL_TAC) >>
     `w2n slot + (type_slot_size elem_tv * (len - 1) + 1) =
      w2n slot + 1 + (len - 1) * type_slot_size elem_tv` by
       (once_rewrite_tac [arithmeticTheory.MULT_COMM] >> decide_tac) >>
     pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  irule contained_ordinary_write_preserves_contract_storage_well_formed >>
  simp[] >>
  qexistsl [`b`, `mid`, `n`, `root_slot`, `st_res`, `tv`,
             `n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv)`,
             `elem_tv`, `v`] >> simp[]
QED


(* Contract endpoint after both writes of dynamic pop. *)
Theorem resolve_array_element_dynamic_pop_final_write_preserves_contract_storage_well_formed:
  !cx mid n b root_slot tv subs st slot elem_tv max st_res len v st1 st2 tenv ty.
    contract_storage_well_formed cx st /\
    storage_layout_safe cx /\
    declared_storage_region cx mid n [] = SOME (b,root_slot,tv) /\
    evaluate_type tenv ty = SOME tv /\
    well_formed_type_value tv /\
    well_formed_type_value elem_tv /\
    0 < type_slot_size elem_tv /\
    w2n (root_slot:bytes32) + type_slot_size tv <= dimword(:256) /\
    slots_in_range (get_storage cx st b) (w2n root_slot) tv /\
    resolve_array_element cx b root_slot tv subs st =
      (INL (slot, ArrayTV elem_tv (Dynamic max), []), st_res) /\
    w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max)) <=
      dimword(:256) /\
    slots_in_range (get_storage cx st_res b) (w2n slot)
      (ArrayTV elem_tv (Dynamic max)) /\
    w2n (read_slot (get_storage cx st_res b) (w2n slot)) = len /\
    0 < len /\
    value_has_type elem_tv v /\
    write_storage_slot cx b
      (n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv))
      elem_tv v st_res = (INL (), st1) /\
    write_storage_slot cx b (n2w (w2n slot)) (BaseTV (UintT 256))
      (IntV (&(len - 1))) st1 = (INL (), st2) ==>
    contract_storage_well_formed cx st2
Proof
  rpt gen_tac >> strip_tac >>
  `len <= max` by
    (qpat_x_assum
       `slots_in_range _ (w2n slot) (ArrayTV elem_tv (Dynamic max))` mp_tac >>
     simp[slots_in_range_def]) >>
  `(len - 1) * type_slot_size elem_tv + type_slot_size elem_tv <=
   max * type_slot_size elem_tv` by
    (irule array_index_element_end_bound >> decide_tac) >>
  `w2n slot + 1 + (len - 1) * type_slot_size elem_tv < dimword(:256)` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `w2n (n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv) : bytes32) =
   w2n slot + 1 + (len - 1) * type_slot_size elem_tv` by simp[] >>
  `w2n slot <=
     w2n (n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv) : bytes32) /\
   w2n (n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv) : bytes32) +
     type_slot_size elem_tv <=
   w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max))` by
    (gvs[vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  `w2n root_slot <=
     w2n (n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv) : bytes32) /\
   w2n (n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv) : bytes32) +
     type_slot_size elem_tv <= w2n root_slot + type_slot_size tv` by
    (irule resolved_write_contained_in_declared_root >> simp[] >>
     conj_tac >- (qexistsl [`tenv`, `ty`] >> simp[]) >>
     qexistsl [`b`, `cx`, `[]`, `ArrayTV elem_tv (Dynamic max)`, `slot`,
               `st`, `st_res`, `subs`] >> simp[]) >>
  `type_slot_size (ArrayTV elem_tv (Dynamic max)) + w2n slot <=
   dimword(:256)` by
    (once_rewrite_tac [arithmeticTheory.ADD_COMM] >>
     qpat_assum
       `w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max)) <= _`
       ACCEPT_TAC) >>
  pop_assum $ mk_asm "pop_final_selected_bound_comm" >>
  `slots_in_range (get_storage cx st1 b) (w2n root_slot) tv` by
    (irule resolve_array_element_dynamic_pop_element_write_preserves_root >>
     simp[] >>
     conj_tac >- (qexistsl [`tenv`, `ty`] >> simp[]) >>
     qexistsl [`elem_tv`, `max`, `slot`, `st`, `st_res`, `subs`, `v`] >>
     simp[] >>
     conj_tac
     >- (asm "pop_final_selected_bound_comm" mp_tac >> EVAL_TAC) >>
     `w2n slot + (type_slot_size elem_tv * (len - 1) + 1) =
      w2n slot + 1 + (len - 1) * type_slot_size elem_tv` by
       (once_rewrite_tac [arithmeticTheory.MULT_COMM] >> decide_tac) >>
     pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  `contract_storage_well_formed cx st1` by
    (drule_all
       resolve_array_element_dynamic_pop_element_write_preserves_contract_storage_well_formed >>
     simp[]) >>
  `len < dimword(:256)` by
    (qpat_x_assum `w2n (read_slot _ (w2n slot)) = len`
       (fn th => once_rewrite_tac [GSYM th]) >>
     MATCH_ACCEPT_TAC wordsTheory.w2n_lt) >>
  `len - 1 < dimword(:256)` by decide_tac >>
  pop_assum $ mk_asm "len_pred_bound" >>
  `value_has_type (BaseTV (UintT 256)) (IntV (&(len - 1)))` by
    (simp[value_has_type_def, integerTheory.NUM_OF_INT,
          integerTheory.INT_POS] >>
     asm "len_pred_bound" mp_tac >>
     qpat_assum `len < dimword(:256)` mp_tac >>
     EVAL_TAC >> decide_tac) >>
  `w2n root_slot <= w2n slot /\
   w2n slot + type_slot_size (BaseTV (UintT 256)) <=
   w2n root_slot + type_slot_size tv` by
    (irule resolved_write_contained_in_declared_root >> simp[] >>
     conj_tac >- (qexistsl [`tenv`, `ty`] >> simp[]) >>
     qexistsl [`b`, `cx`, `[]`, `ArrayTV elem_tv (Dynamic max)`, `slot`,
               `st`, `st_res`, `subs`] >>
     simp[vyperValueTheory.type_slot_size_def]) >>
  `n2w (w2n slot) : bytes32 = slot` by simp[] >>
  pop_assum $ mk_asm "pop_header_slot_eq" >>
  `slots_in_range (get_storage cx st2 b) (w2n root_slot) tv` by
    (irule resolve_array_element_dynamic_pop_two_writes_preserve_root >>
     simp[] >>
     conj_tac >- (qexistsl [`tenv`, `ty`] >> simp[]) >>
     qexistsl [`elem_tv`, `max`, `slot`, `st`, `st1`, `st_res`, `subs`, `v`] >>
     simp[] >>
     conj_tac
     >- (asm "pop_final_selected_bound_comm" mp_tac >> EVAL_TAC) >>
     conj_tac
     >- (asm "pop_header_slot_eq" (fn th => once_rewrite_tac [GSYM th]) >>
         first_assum ACCEPT_TAC) >>
     `w2n slot + (type_slot_size elem_tv * (len - 1) + 1) =
      w2n slot + 1 + (len - 1) * type_slot_size elem_tv` by
       (once_rewrite_tac [arithmeticTheory.MULT_COMM] >> decide_tac) >>
     pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  irule contained_ordinary_write_preserves_contract_storage_well_formed >>
  simp[] >>
  qexistsl [`b`, `mid`, `n`, `root_slot`, `st1`, `tv`,
             `slot`, `BaseTV (UintT 256)`,
             `IntV (&(len - 1))`] >> simp[] >>
  asm "pop_header_slot_eq" (fn th => once_rewrite_tac [GSYM th]) >>
  first_assum ACCEPT_TAC
QED

(* A successful typed write to a semantically declared hashmap leaf preserves
   every declared region.  The same logical leaf is re-established by encoding;
   every other leaf and every ordinary declaration is framed by the explicit
   semantic-region separation conjunct of storage_layout_safe.  This stronger
   region-shaped statement also covers nested hashmap key paths and residual
   structural updates, because assign_target writes the reconstructed whole
   final leaf value. *)
Theorem declared_hashmap_leaf_write_preserves_contract_storage_well_formed:
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  declared_storage_region cx mid n key_subs = SOME (b,slot,tv) /\
  value_has_type tv v /\
  well_formed_type_value tv /\
  write_storage_slot cx b slot tv v st = (INL (),st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  `!mid' n' subs' b' slot' tv' storage st''.
     declared_storage_region cx mid' n' subs' = SOME (b',slot',tv') /\
     get_storage_backend cx b' st' = (INL storage,st'') ==>
     slots_in_range storage (w2n slot') tv'` by
    (rpt gen_tac >> strip_tac >>
     gvs[vyperStorageBackendTheory.get_storage_backend_eq] >>
     `slots_in_range (get_storage cx st b') (w2n slot') tv'` by
       (qpat_x_assum `contract_storage_well_formed cx st` mp_tac >>
        simp[contract_storage_well_formed_def,
             vyperStorageBackendTheory.get_storage_backend_eq] >>
        metis_tac[]) >>
     Cases_on `(mid,n,key_subs) = (mid',n',subs')`
     >- (gvs[] >>
         drule_at (Pat `write_storage_slot`)
           typed_write_storage_slot_establishes_region_forward >>
         simp[]) >>
     `b <> b' \/
      ranges_disjoint (w2n slot) (type_slot_size tv)
                      (w2n slot') (type_slot_size tv')` by
       (Cases_on `b = b'`
        >- (gvs[] >>
            qpat_x_assum `storage_layout_safe cx` mp_tac >>
            simp[storage_layout_safe_def] >> strip_tac >>
            qpat_x_assum
              `!mid1 n1 subs1 mid2 n2 subs2 b slot1 tv1 slot2 tv2. _`
              (qspecl_then
                 [`mid`, `n`, `key_subs`, `mid'`, `n'`, `subs'`, `b`,
                  `slot`, `tv`, `slot'`, `tv'`] mp_tac) >>
            metis_tac[]) >>
        simp[]) >>
     drule typed_write_storage_slot_preserves_disjoint_num_region >>
     disch_then drule >>
     disch_then drule >>
     disch_then irule >>
     (conj_tac >- MATCH_ACCEPT_TAC wordsTheory.w2n_lt) >>
     Cases_on `b` >> Cases_on `b'` >>
     gvs[Excl "ranges_disjoint_def"]) >>
  simp[contract_storage_well_formed_def] >>
  conj_tac
  >- (simp[well_formed_storage_def, storage_var_in_range_def] >>
      rpt gen_tac >> strip_tac >>
      `declared_storage_region cx mid' n' [] =
         SOME (is_transient,n2w off,tv')` by
        (irule declared_storage_region_ordinary >> simp[]) >>
      Cases_on `off < dimword(:256)`
      >- (qpat_assum
            `!m name subs bb sl ty stor s. _`
            (qspecl_then
               [`mid'`, `n'`, `[]`, `is_transient`, `n2w off`, `tv'`,
                `storage`, `st''`] mp_tac) >>
          simp[vyperStorageBackendTheory.get_storage_backend_eq,
               wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
      `off + type_slot_size tv' <= dimword(:256)` by
        (qpat_x_assum `storage_layout_safe cx` mp_tac >>
         simp[storage_layout_safe_def, well_formed_layout_def] >>
         metis_tac[]) >>
      `off = dimword(:256) /\ type_slot_size tv' = 0` by decide_tac >>
      irule (CONJUNCT1 zero_slot_size_slots_in_range) >> simp[]) >>
  metis_tac[]
QED


(* Exact HashMapRef branch adapter.  The interpreter's split/hash/evaluate
   computation identifies the same semantic declared leaf; any residual
   array/struct subscripts have already reconstructed a value of final_tv
   before this one whole-leaf write. *)
Theorem hashmapref_leaf_write_preserves_contract_storage_well_formed:
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  get_module_code cx mid = SOME code /\
  find_var_decl_by_num (string_to_num n) code =
    SOME (HashMapVarDecl b kt vt,id) /\
  lookup_var_slot_from_layout cx b mid id = SOME off /\
  split_hashmap_subscripts vt rest_subs = SOME (final_type,kts,[]) /\
  compute_hashmap_slot (n2w off) (kt::kts) (first_sub::rest_subs) =
    SOME final_slot /\
  evaluate_type (get_tenv cx) final_type = SOME final_tv /\
  value_has_type final_tv v /\
  write_storage_slot cx b final_slot final_tv v st = (INL (),st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  irule declared_hashmap_leaf_write_preserves_contract_storage_well_formed >>
  conj_tac >- simp[] >>
  qexistsl [`b`, `first_sub::rest_subs`, `mid`, `n`, `final_slot`, `st`,
            `final_tv`, `v`] >>
  simp[] >>
  conj_tac
  >- metis_tac[CONJUNCT1 vyperTypingTheory.evaluate_type_well_formed] >>
  irule declared_hashmap_leaf_agrees_assign_target >> simp[]
QED


(* Whole-variable replacement is the corresponding successful typed primitive
   write.  This consumer-shaped form keeps monadic unfolding out of the
   contract-level framing proof below. *)
Theorem update_toplevel_name_typed_write[local]:
  storage_var_info cx mid n = SOME (b,off,tv) /\
  value_has_type tv v ==>
  write_storage_slot cx b (n2w off) tv v st =
    (INL (),update_toplevel_name cx st mid n v)
Proof
  rpt strip_tac >>
  drule vyperStorageFrameTheory.update_toplevel_name_eq_write >>
  disch_then (qspecl_then [`st`, `v`] assume_tac) >>
  drule (CONJUNCT1 vyperTypingTheory.value_has_type_equiv) >> strip_tac >>
  Cases_on `encode_value tv v` >>
  gvs[vyperStorageBackendTheory.write_storage_slot_eq]
QED

(* Whole top-level replacement preserves both ordinary declared ranges and all
   semantically declared hashmap leaves.  The latter are framed by the exact
   semantic-region separation conjunct of storage_layout_safe. *)
Theorem update_toplevel_name_preserves_contract_storage_well_formed:
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  storable_value cx mid n v /\
  var_in_storage cx mid n ==>
  contract_storage_well_formed cx (update_toplevel_name cx st mid n v)
Proof
  rpt strip_tac >>
  `well_formed_storage cx (update_toplevel_name cx st mid n v)` by
    (irule update_toplevel_name_preserves_well_formed_storage >>
     simp[contract_storage_well_formed_storage,
          storage_layout_safe_layout]) >>
  simp[contract_storage_well_formed_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[vyperStorageBackendTheory.get_storage_backend_eq] >>
  drule var_in_storage_storage_var_info >> strip_tac >>
  rename1 `storage_var_info cx mid n = SOME (b1,off1,tv1)` >>
  `value_has_type tv1 v` by
    (qpat_x_assum `storable_value cx mid n v` mp_tac >>
     simp[storable_value_def, storage_type_of_def]) >>
  `declared_storage_region cx mid n [] = SOME (b1,n2w off1,tv1)` by
    (irule declared_storage_region_ordinary >> simp[]) >>
  `write_storage_slot cx b1 (n2w off1) tv1 v st =
     (INL (),update_toplevel_name cx st mid n v)` by
    (irule update_toplevel_name_typed_write >> simp[]) >>
  `slots_in_range (get_storage cx st b) (w2n slot) tv` by
    (qpat_x_assum `contract_storage_well_formed cx st` mp_tac >>
     simp[contract_storage_well_formed_def,
          vyperStorageBackendTheory.get_storage_backend_eq] >>
     metis_tac[]) >>
  Cases_on `(mid,n,[]) = (mid',n',subs)`
  >- (gvs[] >>
      drule_at (Pat `write_storage_slot`)
        typed_write_storage_slot_establishes_region_forward >>
      simp[]) >>
  `b1 <> b \/
   ranges_disjoint (w2n (n2w off1 : bytes32)) (type_slot_size tv1)
                   (w2n slot) (type_slot_size tv)` by
    (Cases_on `b1 = b` >> gvs[] >>
     qpat_x_assum `storage_layout_safe cx` mp_tac >>
     simp[storage_layout_safe_def] >> strip_tac >>
     qpat_x_assum
       `!mid1 n1 subs1 mid2 n2 subs2 b slot1 tv1 slot2 tv2. _`
       (qspecl_then [`mid`, `n`, `[]`, `mid'`, `n'`, `subs`, `b`,
                    `n2w off1`, `tv1`, `slot`, `tv`] mp_tac) >>
     strip_tac >> gvs[]) >>
  drule_at (Pat `slots_in_range`)
    typed_write_storage_slot_preserves_disjoint_num_region >>
  disch_then
    (qspecl_then [`v`, `tv1`, `update_toplevel_name cx st mid n v`,
                  `n2w off1`, `b1`] mp_tac) >>
  (impl_tac >- simp[wordsTheory.w2n_lt]) >> simp[]
QED


(* Explicit two-write closure for sequential whole-variable replacement.  The
   second premise is checked in the state produced by the first write; no
   atomicity or abstract preservation relation is assumed. *)
Theorem update_toplevel_name_twice_preserves_contract_storage_well_formed:
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  storable_value cx mid1 n1 v1 /\ var_in_storage cx mid1 n1 /\
  storable_value cx mid2 n2 v2 /\ var_in_storage cx mid2 n2 ==>
  contract_storage_well_formed cx
    (update_toplevel_name cx
       (update_toplevel_name cx st mid1 n1 v1) mid2 n2 v2)
Proof
  rpt strip_tac >>
  irule update_toplevel_name_preserves_contract_storage_well_formed >>
  simp[] >>
  irule update_toplevel_name_preserves_contract_storage_well_formed >>
  simp[]
QED

(* Consumer-shaped cons rule: after the explicit head replacement establishes
   the invariant, any already-proved tail preservation implication composes
   without hiding the tail operation behind a new predicate. *)
Theorem update_toplevel_name_contract_storage_cons:
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  storable_value cx mid n v /\
  var_in_storage cx mid n /\
  (contract_storage_well_formed cx
     (update_toplevel_name cx st mid n v) ==>
   contract_storage_well_formed cx st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >> first_x_assum irule >>
  irule update_toplevel_name_preserves_contract_storage_well_formed >>
  simp[]
QED
val _ = export_theory();
