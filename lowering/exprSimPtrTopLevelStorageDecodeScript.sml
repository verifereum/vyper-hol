(* Robust decoding depends only on the live bytes of the copied value. *)
Theory exprSimPtrTopLevelStorageDecode
Ancestors
  storageDecodeMemory bodyPtrDefs valueEncodingProofs valueEncoding
  vyperValue vyperLookupStorage accountsRelProps list pred_set

Theorem toplevel_storage_live_memory_perturb:
  storage_live_memory st bs tv dst mem /\
  (!i j. i < type_slot_size tv /\ j < 32 /\ dst + 32*i+j IN tainted ==>
         dead_bytes st bs tv (bs+i) j) /\
  mem_agree_outside tainted mem mem' ==>
  storage_live_memory st bs tv dst mem'
Proof
  simp[storage_live_memory_def, copy_bytes_def] >> rpt strip_tac >>
  `dst + (32*i+b) NOTIN tainted` by metis_tac[] >>
  `mem_bytes_at (dst + (32*i+b)) 1 mem =
   mem_bytes_at (dst + (32*i+b)) 1 mem'` by
    metis_tac[mem_agree_outside_def] >>
  qpat_x_assum `!i b. _ ==> EL _ _ = _` drule_all >>
  disch_then (fn th => assume_tac th) >>
  qpat_x_assum `mem_bytes_at _ 1 _ = _` (mp_tac o Q.AP_TERM `EL 0`) >>
  gvs[EL_mem_bytes_at]
QED

Theorem toplevel_storage_decode_robust:
  well_formed_type_value tv /\ slots_in_range st bs tv /\
  decode_value st bs tv = SOME v /\ storage_live_memory st bs tv dst mem /\
  (!i j. i < type_slot_size tv /\ j < 32 /\ dst+32*i+j IN tainted ==>
         dead_bytes st bs tv (bs+i) j) ==>
  !mem'. mem_agree_outside tainted mem mem' ==> val_in_memory tv v dst mem'
Proof
  rpt strip_tac >> irule decode_value_live_memory >>
  simp[] >> qexistsl_tac [`bs`, `st`] >> simp[] >>
  irule toplevel_storage_live_memory_perturb >> metis_tac[]
QED
