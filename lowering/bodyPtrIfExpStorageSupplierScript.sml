Theory bodyPtrIfExpStorageSupplier
Ancestors accountsRelProps compileEnv vyperStorage vyperLookupStorage
  vyperValue words arithmetic bodyPtrIfExpStorageRobust valueEncodingProofs
  valueEncodingProps storageDecodeMemory bodyPtrDefs venomMemProofs pred_set

Theorem ifexp_storage_range_read_head:
  storage_range_agree st rt w ty /\ 0 < type_slot_size ty ==>
  read_slot rt (w2n w) = read_slot st (w2n w)
Proof
  strip_tac >> drule_all storage_range_agree_head >>
  simp[read_slot_def]
QED

Theorem ifexp_storage_range_bytes_length:
  storage_range_agree st rt w (BaseTV (BytesT (Dynamic max))) /\
  slots_in_range st (w2n w) (BaseTV (BytesT (Dynamic max))) ==>
  slots_in_range rt (w2n w) (BaseTV (BytesT (Dynamic max))) /\
  w2n (read_slot rt (w2n w)) = w2n (read_slot st (w2n w))
Proof
  strip_tac >>
  `read_slot rt (w2n w) = read_slot st (w2n w)` by
    (irule ifexp_storage_range_read_head >>
     qexists_tac `BaseTV (BytesT (Dynamic max))` >>
     simp[type_slot_size_def]) >>
  gvs[slots_in_range_def]
QED

Theorem ifexp_storage_range_dead_bytes:
  storage_range_agree st rt w ty ==>
  (dead_bytes rt (w2n w) ty j b <=> dead_bytes st (w2n w) ty j b)
Proof
  strip_tac >> irule (cj 1 dead_bytes_live_frame) >>
  gvs[storage_range_agree_def] >> rpt strip_tac >>
  `i < dimword (:256)` by decide_tac >>
  first_x_assum (qspec_then `n2w i : bytes32` mp_tac) >>
  simp[w2n_n2w, LESS_MOD]
QED

Theorem ifexp_range_storage_decode_robust:
  well_formed_type_value ty /\ slots_in_range st (w2n w) ty /\
  decode_value st (w2n w) ty = SOME v /\
  storage_range_agree st rt w ty /\
  (!i. i < type_slot_size ty ==>
    mem_word_at (dst+32*i) mem = lookup_storage (w+n2w i) rt) /\
  (!i b. i < type_slot_size ty /\ b < 32 /\ dst+32*i+b IN dest_taint ==>
    (w+n2w i,b) IN source_taint) /\
  (!k b. w2n w <= w2n k /\ w2n k < w2n w+type_slot_size ty /\
    b < 32 /\ (k,b) IN source_taint ==>
    dead_bytes rt (w2n w) ty (w2n k) b) ==>
  !m. mem_agree_outside dest_taint mem m ==> val_in_memory ty v dst m
Proof
  rpt strip_tac >> irule ifexp_storage_decode_robust >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`w2n w`,`mem`,`st`,`dest_taint`] >> simp[] >>
  conj_tac >- suspend "taint" >>
  simp[storage_live_memory_def, copy_bytes_def] >> rpt strip_tac >>
  qpat_x_assum `!i. i < _ ==> _` drule >> strip_tac >>
  simp[valueEncodingProofsTheory.mem_bytes_at_word] >>
  qpat_x_assum `storage_range_agree _ _ _ _` mp_tac >>
  simp[storage_range_agree_def] >> strip_tac >>
  `w2n w + i < dimword (:256)` by decide_tac >>
  `w2n (w + n2w i) = w2n w + i /\
   (n2w (w2n w + i) : bytes32) = w + n2w i /\
   (n2w (i + w2n w) : bytes32) = w + n2w i` by
    (Cases_on `w` >> fs[wordsTheory.word_add_n2w]) >>
  first_x_assum (qspecl_then [`w + n2w i`, `b`] mp_tac) >>
  simp[read_slot_def]
QED

Resume ifexp_range_storage_decode_robust[taint]:
  rpt strip_tac >>
  `w2n w+type_slot_size ty <= dimword(:256)` by
    metis_tac[storage_range_agree_def] >>
  `w2n w+i < dimword(:256)` by decide_tac >>
  `w2n (w+n2w i) = w2n w+i` by
    (Cases_on `w` >> fs[wordsTheory.word_add_n2w]) >>
  `(w+n2w i,b) IN source_taint` by metis_tac[ADD_COMM] >>
  drule ifexp_storage_range_dead_bytes >> strip_tac >>
  qpat_x_assum `!k b. _` (qspecl_then [`w+n2w i`,`b`] mp_tac) >>
  simp[] >> metis_tac[ADD_COMM]
QED

Finalise ifexp_range_storage_decode_robust
