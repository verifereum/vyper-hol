(* Primitive typed storage-write preservation. *)

Theory vyperStorageWritePreservation
Ancestors
  vyperStorageLayoutSafety vyperStorageFrame vyperLookupStorage
  vyperState vyperStorageBackend
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

val _ = export_theory();
