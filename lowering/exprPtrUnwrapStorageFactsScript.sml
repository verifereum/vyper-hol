(* Live storage bytes remain represented under perturbation of dead bytes. *)
Theory exprPtrUnwrapStorageFacts
Ancestors
  storageDecodeMemory bodyPtrDefs valueEncodingProofs accountsRelProps
  abiDecodeStaticProps

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

Theorem ptr_vv_ok_storage_taint:
  !cx t tv t' p es G tn s w ty k b.
    ptr_vv_ok cx t tv (LocatedValue t' p) es G tn s /\
    eval_operand p.ptr_operand s = SOME w /\
    evaluate_type (get_tenv cx) t = SOME ty /\
    w2n w <= w2n k /\ w2n k < w2n w + type_slot_size ty /\ b < 32 ==>
    (p.ptr_location = LocStorage /\ (k,b) IN tn.t_stor ==>
      dead_bytes (s.vs_accounts s.vs_call_ctx.cc_address).storage
        (w2n w) ty (w2n k) b) /\
    (p.ptr_location = LocTransient /\ (k,b) IN tn.t_trans ==>
      dead_bytes (s.vs_transient s.vs_call_ctx.cc_address)
        (w2n w) ty (w2n k) b)
Proof
  simp[ptr_vv_ok_def] >> metis_tac[]
QED

Theorem storage_range_agree_dead_bytes:
  !st rt w tv j b.
    storage_range_agree st rt w tv ==>
    (dead_bytes rt (w2n w) tv j b <=> dead_bytes st (w2n w) tv j b)
Proof
  rpt strip_tac >> irule (cj 1 dead_bytes_live_frame) >>
  gvs[storage_range_agree_def] >> rpt strip_tac >>
  `i < dimword (:256)` by decide_tac >>
  first_x_assum (qspecl_then [`n2w i`, `c`] mp_tac) >>
  simp[wordsTheory.w2n_n2w]
QED

Theorem storage_range_copied_live_memory:
  !st rt w tv dst mem.
    storage_range_agree st rt w tv /\
    (!i. i < type_slot_size tv ==>
      mem_word_at (dst + 32*i) mem = lookup_storage (w + n2w i) rt) ==>
    storage_live_memory st (w2n w) tv dst mem
Proof
  rpt gen_tac >> strip_tac >>
  simp[storage_live_memory_def, copy_bytes_def] >> rpt strip_tac >>
  `w2n w + type_slot_size tv <= dimword (:256)` by
    gvs[storage_range_agree_def] >>
  `w2n w + i < dimword (:256)` by decide_tac >>
  `w2n (w + n2w i) = w2n w + i` by
    (irule w2n_add_n2w_lt >> simp[]) >>
  qpat_x_assum `!i. i < _ ==> _` drule >> strip_tac >>
  simp[mem_bytes_at_word] >>
  qpat_x_assum `storage_range_agree _ _ _ _` mp_tac >>
  simp[storage_range_agree_def] >> strip_tac >>
  first_x_assum (qspecl_then [`w + n2w i`, `b`] mp_tac) >>
  simp[vyperStorageTheory.read_slot_def] >>
  Cases_on `w` >> fs[wordsTheory.word_add_n2w, arithmeticTheory.ADD_COMM]
QED

(* Word equality and taint containment are independent copy obligations. *)
Theorem storage_range_copied_robust:
  !st rt w tv v dst mem m.
    well_formed_type_value tv /\ slots_in_range st (w2n w) tv /\
    decode_value st (w2n w) tv = SOME v /\
    storage_range_agree st rt w tv /\
    (!i. i < type_slot_size tv ==>
      mem_word_at (dst + 32*i) mem = lookup_storage (w + n2w i) rt) /\
    (!i b. i < type_slot_size tv /\ b < 32 /\ dst + 32*i + b IN m ==>
      dead_bytes rt (w2n w) tv (w2n w+i) b) ==>
    !mem'. mem_agree_outside m mem mem' ==> val_in_memory tv v dst mem'
Proof
  rpt gen_tac >> strip_tac >>
  `storage_live_memory st (w2n w) tv dst mem` by
    (irule storage_range_copied_live_memory >> qexists `rt` >> simp[]) >>
  drule storage_range_agree_dead_bytes >> strip_tac >>
  rpt strip_tac >> irule storage_live_memory_robust >>
  simp[] >> qexistsl [`w2n w`, `m`, `mem`, `st`] >>
  gvs[arithmeticTheory.ADD_COMM] >> metis_tac[]
QED
