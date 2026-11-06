Theory bodyPtrIfExpStorageRobust
Ancestors
  storageDecodeMemory bodyPtrDefs venomMemProofs valueEncodingProps valueEncodingProofs
  pred_set list arithmetic

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
