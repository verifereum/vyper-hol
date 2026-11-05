(* Live storage bytes remain represented under perturbation of dead bytes. *)
Theory exprPtrUnwrapStorageFacts
Ancestors
  storageDecodeMemory bodyPtrDefs valueEncodingProofs

Theorem copy_bytes_mem_agree_outside:
  !st bs n D dst mem m mem'.
    copy_bytes st bs n D dst mem /\
    (!i b. i < n /\ b < 32 /\ dst + 32*i + b IN m ==>
       D (bs+i) b) /\
    mem_agree_outside m mem mem' ==>
    copy_bytes st bs n D dst mem'
Proof
  rpt gen_tac >>
  simp[copy_bytes_def, mem_agree_outside_def] >> rpt strip_tac >>
  `dst + 32*i + b NOTIN m` by
    (simp[arithmeticTheory.ADD_COMM] >> metis_tac[]) >>
  first_x_assum (drule_then assume_tac) >>
  pop_assum (mp_tac o Q.AP_TERM `EL 0`) >>
  simp[EL_mem_bytes_at] >> strip_tac >>
  gvs[EL_mem_bytes_at] >> metis_tac[]
QED

Theorem storage_live_memory_robust:
  !st bs tv v dst mem m.
    well_formed_type_value tv /\ slots_in_range st bs tv /\
    decode_value st bs tv = SOME v /\
    storage_live_memory st bs tv dst mem /\
    (!i b. i < type_slot_size tv /\ b < 32 /\
       dst + 32*i + b IN m ==> dead_bytes st bs tv (bs+i) b) ==>
    !mem'. mem_agree_outside m mem mem' ==> val_in_memory tv v dst mem'
Proof
  rpt strip_tac >> irule decode_value_live_memory >>
  simp[] >> qexistsl [`bs`, `st`] >> simp[] >>
  gvs[storage_live_memory_def] >>
  irule copy_bytes_mem_agree_outside >>
  qexistsl [`m`, `mem`] >> simp[arithmeticTheory.ADD_COMM]
QED
