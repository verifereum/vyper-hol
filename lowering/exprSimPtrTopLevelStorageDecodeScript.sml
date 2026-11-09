(* Robust decoding depends only on the live bytes of the copied value. *)
Theory exprSimPtrTopLevelStorageDecode
Ancestors
  storageDecodeMemory bodyPtrDefs valueEncodingProofs valueEncoding
  vyperValue vyperLookupStorage accountsRelProps list pred_set
  exprSimPtrTopLevelStorageCopy exprSimStorageCopy abiEncoderMemory words
Libs
  Omega

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

Theorem toplevel_copy_prefix_live_memory:
  (loc = LocStorage \/ loc = LocTransient) /\ n = type_slot_size tv /\
  w2n a + n <= dimword (:256) /\ copy_prefix loc a b n s n t /\
  (!i. i < n ==> copy_runtime_word loc s (a+n2w i) =
       read_slot st (w2n a+i)) ==>
  storage_live_memory st (w2n a) tv b t.vs_memory
Proof
  rpt strip_tac >> simp[storage_live_memory_def, copy_bytes_def] >>
  rpt strip_tac >> simp[abi_encoder_word_window] >>
  `i < n` by metis_tac[] >>
  drule_all copy_prefix_word >> disch_then SUBST1_TAC >>
  `copy_runtime_word loc s (a+n2w i) = read_slot st (w2n a+i)` by metis_tac[] >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem toplevel_copy_taint_dead_bytes:
  tainted SUBSET toplevel_copy_taint_bound loc a b tn n /\
  (!i j. i < n /\ j < 32 /\
     (a+n2w i,j) IN toplevel_copy_source_taint loc tn ==>
     dead_bytes st bs tv (bs+i) j) ==>
  !i j. i < n /\ j < 32 /\ b+32*i+j IN tainted ==>
    dead_bytes st bs tv (bs+i) j
Proof
  simp[toplevel_copy_taint_bound_def, toplevel_copy_region_def,
    toplevel_copy_translated_taint_def, SUBSET_DEF] >>
  rpt strip_tac >>
  `b <= b+32*i+j /\ b+32*i+j < b+32*n` by decide_tac >>
  qpat_x_assum `!x. x IN tainted ==> _`
    (qspec_then `b+32*i+j` mp_tac) >> simp[] >>
  disch_then (qx_choosel_then [`k`,`l`] strip_assume_tac) >>
  `i = k /\ j = l` by
    (qpat_x_assum `32*i+j = 32*k+l` mp_tac >>
     qpat_x_assum `j < 32` mp_tac >> qpat_x_assum `l < 32` mp_tac >>
     Omega.OMEGA_TAC) >> gvs[]
QED

Theorem toplevel_copy_prefix_decode_robust:
  (loc = LocStorage \/ loc = LocTransient) /\ n = type_slot_size tv /\
  w2n a + n <= dimword (:256) /\ copy_prefix loc a b n s n t /\
  (!i. i < n ==> copy_runtime_word loc s (a+n2w i) =
       read_slot st (w2n a+i)) /\
  well_formed_type_value tv /\ slots_in_range st (w2n a) tv /\
  decode_value st (w2n a) tv = SOME v /\
  tnf.t_mem SUBSET toplevel_copy_taint_bound loc a b tn n /\
  (!i j. i < n /\ j < 32 /\
     (a+n2w i,j) IN toplevel_copy_source_taint loc tn ==>
     dead_bytes st (w2n a) tv (w2n a+i) j) ==>
  !mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
    val_in_memory tv v b mem
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `storage_live_memory st (w2n a) tv b t.vs_memory` by
    (irule toplevel_copy_prefix_live_memory >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `!i j. i < type_slot_size tv /\ j < 32 /\ b+32*i+j IN tnf.t_mem ==>
     dead_bytes st (w2n a) tv (w2n a+i) j` by
    (qpat_x_assum `n = type_slot_size tv` (SUBST_ALL_TAC o SYM) >>
     metis_tac[toplevel_copy_taint_dead_bytes]) >>
  metis_tac[toplevel_storage_decode_robust]
QED
