Theory bodyPtrIfExpStorageRobust
Ancestors
  storageDecodeMemory bodyPtrDefs venomMemProofs valueEncodingProps valueEncodingProofs
  pred_set list arithmetic accountsRelProps compileEnv words

Theorem ifexp_storage_live_memory_taint_frame:
  storage_live_memory st bs tv dst mem /\
  (!i b. i < type_slot_size tv /\ b < 32 /\ dst+32*i+b IN tainted ==>
    dead_bytes st bs tv (bs+i) b) /\
  mem_agree_outside tainted mem m ==>
  storage_live_memory st bs tv dst m
Proof
  simp[storage_live_memory_def, copy_bytes_def] >> rpt strip_tac >>
  `dst+32*i+b NOTIN tainted` by metis_tac[ADD_COMM] >>
  `mem_bytes_at (dst+32*i+b) 1 mem = mem_bytes_at (dst+32*i+b) 1 m` by
    metis_tac[mem_agree_outside_def] >>
  `EL 0 (mem_bytes_at (dst+32*i+b) 1 mem) =
   EL 0 (mem_bytes_at (dst+32*i+b) 1 m)` by simp[] >>
  fs[EL_mem_bytes_at] >> metis_tac[]
QED

Theorem ifexp_storage_decode_robust:
  well_formed_type_value tv /\ slots_in_range st bs tv /\
  decode_value st bs tv = SOME v /\ storage_live_memory st bs tv dst mem /\
  (!i b. i < type_slot_size tv /\ b < 32 /\ dst+32*i+b IN tainted ==>
    dead_bytes st bs tv (bs+i) b) ==>
  !m. mem_agree_outside tainted mem m ==> val_in_memory tv v dst m
Proof
  rpt strip_tac >> irule decode_value_live_memory >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`bs`,`st`] >> simp[] >>
  irule ifexp_storage_live_memory_taint_frame >> metis_tac[]
QED

Theorem ifexp_storage_taint_dead_byte:
  storage_read_live cx tr st w tv /\
  storage_agree (storage_dead cx tr st) st rt /\
  (!key b. (key,b) IN source_taint ==> storage_dead cx tr rt (w2n key) b) /\
  i < type_slot_size tv /\ (w+n2w i,b) IN source_taint ==>
  dead_bytes st (w2n w) tv (w2n w+i) b
Proof
  strip_tac >> drule_all storage_agree_storage_dead >> strip_tac >>
  `storage_dead cx tr st (w2n (w+n2w i)) b` by metis_tac[] >>
  `w2n w + type_slot_size tv <= dimword(:256)` by
    metis_tac[storage_read_live_def] >>
  `w2n w+i < dimword(:256)` by decide_tac >>
  `w2n (w+n2w i) = w2n w+i` by
    (Cases_on `w` >> fs[wordsTheory.word_add_n2w]) >>
  `storage_dead cx tr st (w2n w+i) b` by metis_tac[] >>
  qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[storage_read_live_def] >>
  disch_then drule >> simp[] >> decide_tac
QED

Theorem ifexp_copied_storage_decode_robust:
  well_formed_type_value tv /\ slots_in_range st (w2n w) tv /\
  decode_value st (w2n w) tv = SOME v /\
  storage_read_live cx tr st w tv /\
  storage_agree (storage_dead cx tr st) st rt /\
  (!key b. (key,b) IN source_taint ==> storage_dead cx tr rt (w2n key) b) /\
  (!i. i < type_slot_size tv ==>
    mem_word_at (dst+32*i) mem = lookup_storage (w+n2w i) rt) /\
  (!i b. i < type_slot_size tv /\ b < 32 /\ dst+32*i+b IN dest_taint ==>
    (w+n2w i,b) IN source_taint) ==>
  !m. mem_agree_outside dest_taint mem m ==> val_in_memory tv v dst m
Proof
  rpt strip_tac >> irule ifexp_storage_decode_robust >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`w2n w`,`mem`,`st`,`dest_taint`] >> simp[] >>
  conj_tac >-
    (rpt strip_tac >>
     once_rewrite_tac[ADD_COMM] >> irule ifexp_storage_taint_dead_byte >>
     metis_tac[ADD_COMM]) >>
  irule copied_storage_live_memory >> metis_tac[]
QED
