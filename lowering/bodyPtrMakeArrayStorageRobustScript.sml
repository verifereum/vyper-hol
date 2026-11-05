(* Only live bytes of a decoded storage value need to be untainted. *)
Theory bodyPtrMakeArrayStorageRobust
Ancestors
  storageDecodeMemory bodyPtrDefs valueEncodingProps valueEncodingProofs list

Theorem copy_bytes_mem_agree_outside:
  copy_bytes st bs n D dst mem /\
  (!i j. i < n /\ j < 32 /\ ~D (bs+i) j ==>
    dst+32*i+j NOTIN tainted) /\
  mem_agree_outside tainted mem m ==>
  copy_bytes st bs n D dst m
Proof
  simp[copy_bytes_def] >> rpt strip_tac >>
  `dst+32*i+b NOTIN tainted` by metis_tac[arithmeticTheory.ADD_ASSOC] >>
  `mem_bytes_at (dst+32*i+b) 1 mem =
   mem_bytes_at (dst+32*i+b) 1 m` by
    metis_tac[mem_agree_outside_def] >>
  `EL 0 (mem_bytes_at (dst+32*i+b) 1 mem) =
   EL 0 (mem_bytes_at (dst+32*i+b) 1 m)` by simp[] >>
  gvs[EL_mem_bytes_at] >> metis_tac[]
QED

Theorem storage_live_memory_robust_decode:
  well_formed_type_value tv /\ slots_in_range st bs tv /\
  decode_value st bs tv = SOME v /\
  storage_live_memory st bs tv dst mem /\
  (!i j. i < type_slot_size tv /\ j < 32 /\ dst+32*i+j IN tainted ==>
    dead_bytes st bs tv (bs+i) j) ==>
  !m. mem_agree_outside tainted mem m ==> val_in_memory tv v dst m
Proof
  rpt strip_tac >> irule decode_value_live_memory >> simp[] >>
  qexistsl_tac [`bs`, `st`] >> simp[] >>
  gvs[storage_live_memory_def] >>
  irule copy_bytes_mem_agree_outside >>
  qexistsl_tac [`mem`, `tainted`] >> simp[] >>
  metis_tac[arithmeticTheory.ADD_ASSOC]
QED
