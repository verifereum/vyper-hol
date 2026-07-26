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

Theorem evaluate_type_ArrayTV_inv[local]:
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

val _ = export_theory();
