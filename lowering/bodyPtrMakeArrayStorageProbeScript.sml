(* Probe the source address ADD plus external load with arbitrary provenance.
   Retaining the real intermediate ghost avoids a false scalar-only interface. *)
Theory bodyPtrMakeArrayStorageProbe
Ancestors
  bodyPtrMakeArrayStorageBody bodyPtrMakeArrayAdd typedCopyPtr
  ptrDiscipline venomState fragGasPathPtr finite_map accountsRelProps words
  storageDecodeMemory valueEncodingProofs vyperStorage bodyPtrMakeArrayStorageRobust
  exprPtrUnwrapStorageFacts

Theorem copied_storage_range_live_memory:
  storage_range_agree st rt a tv /\
  (!i. i < type_slot_size tv ==>
    mem_word_at (dst+32*i) mem = lookup_storage (a+n2w i) rt) ==>
  storage_live_memory st (w2n a) tv dst mem
Proof
  strip_tac >> simp[storage_live_memory_def, copy_bytes_def] >>
  rpt strip_tac >>
  `w2n a+i < dimword (:256)` by
    (fs[storage_range_agree_def] >> decide_tac) >>
  `w2n (a+n2w i) = w2n a+i` by
    (Cases_on `a` >> fs[word_add_n2w]) >>
  qpat_x_assum `!i. i < _ ==> _` drule >> strip_tac >>
  simp[valueEncodingProofsTheory.mem_bytes_at_word] >>
  qpat_x_assum `storage_range_agree _ _ _ _` mp_tac >>
  simp[storage_range_agree_def] >> strip_tac >>
  first_x_assum (qspecl_then [`a+n2w i`, `b`] mp_tac) >>
  simp[read_slot_def] >> Cases_on `a` >>
  fs[word_add_n2w, arithmeticTheory.ADD_COMM]
QED

Theorem copied_storage_range_robust_decode:
  well_formed_type_value tv /\ slots_in_range st (w2n a) tv /\
  decode_value st (w2n a) tv = SOME v /\ storage_range_agree st rt a tv /\
  (!i. i < type_slot_size tv ==>
    mem_word_at (dst+32*i) mem = lookup_storage (a+n2w i) rt) /\
  (!i j. i < type_slot_size tv /\ j < 32 /\ dst+32*i+j IN tainted ==>
    j IN key_taint keys (a+n2w i)) /\
  (!k j. w2n a <= w2n k /\ w2n k < w2n a+type_slot_size tv /\
    j < 32 /\ j IN key_taint keys k ==>
    dead_bytes rt (w2n a) tv (w2n k) j) ==>
  !m. mem_agree_outside tainted mem m ==> val_in_memory tv v dst m
Proof
  strip_tac >> match_mp_tac storage_live_memory_robust_decode >>
  qexistsl_tac [`w2n a`, `st`] >> simp[] >>
  conj_tac
  >- (irule copied_storage_range_live_memory >> metis_tac[]) >>
  rpt strip_tac >>
  `w2n a+i < dimword (:256)` by
    (fs[storage_range_agree_def] >> decide_tac) >>
  `w2n (a+n2w i) = w2n a+i` by
    (Cases_on `a` >> fs[word_add_n2w]) >>
  `j IN key_taint keys (a+n2w i)` by
    metis_tac[arithmeticTheory.ADD_ASSOC] >>
  `dead_bytes rt (w2n a) tv (w2n a+i) j` by
    (qpat_x_assum `!k j. _` (qspecl_then [`a+n2w i`, `j`] mp_tac) >> simp[]) >>
  drule storage_range_agree_dead_bytes >>
  disch_then (qspecl_then [`i+w2n a`, `j`] (irule o iffLR)) >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC
QED
