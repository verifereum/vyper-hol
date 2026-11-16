(* Live-support storage taint, independent of compiled execution. *)
Theory fullStoreCopyTaint
Ancestors
  fullStoreCopyEndpoint placeStoreSlots ptrDiscipline loweringStateRelDefs
  accountsRelProps vyperStorageFrame vyperEncodeDecode
  finite_map pred_set list rich_list arithmetic words

Theorem store_copy_live_taint_bound:
  !ks ta0. FOLDL (\ta i. key_update ta ((k:bytes32)+n2w i)
        (mem_word_taint M (off+32*i))) ta0 ks SUBSET
    (ta0 DIFF {(k+n2w i,b) | (i,b) | MEM i ks}) UNION
    {(k+n2w i,b) | MEM i ks /\ b<32 /\ off+32*i+b IN M}
Proof
  Induct using SNOC_INDUCT >- simp[] >>
  simp[FOLDL_SNOC] >>
  fs[SUBSET_DEF, key_update_def, mem_word_taint_def] >>
  rpt strip_tac
  >- (first_x_assum drule >> strip_tac >> gvs[] >> metis_tac[]) >>
  disj2_tac >> qexists_tac `x` >> simp[ADD_COMM]
QED

Theorem storage_dead_endpoint_outside[local]:
  !cx tr mid n subs k tv st final x b.
    declared_storage_region cx mid n subs = SOME (tr,k,tv) /\
    MEM (tr,k,tv) (FST H) /\
    (!i. i < dimword (:256) /\
         ~(w2n k <= i /\ i < w2n k + type_slot_size tv) ==>
         lookup_storage (n2w i) final = lookup_storage (n2w i) st) /\
    ~(w2n k <= x /\ x < w2n k + type_slot_size tv) /\
    storage_dead H tr st x b ==>
    storage_dead H tr final x b
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `storage_dead _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[storage_dead_def] >> strip_tac >>
  rename1 `dead_bytes st (w2n slot) tv' x b` >>
  `(slot:bytes32,tv') <> (k,tv)` by
    (strip_tac >> gvs[] >> drule (cj 1 dead_bytes_range) >> simp[]) >>
  `ranges_disjoint (w2n slot) (type_slot_size tv')
     (w2n k) (type_slot_size tv)` by
    (first_x_assum irule >> metis_tac[]) >>
  `dead_bytes final (w2n slot) tv' x b <=>
   dead_bytes st (w2n slot) tv' x b` by
    (irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
     first_x_assum irule >>
     qpat_x_assum `ranges_disjoint _ _ _ _` mp_tac >>
     rewrite_tac[vyperStorageFrameTheory.ranges_disjoint_def] >>
     rpt strip_tac >> gvs[] >> decide_tac) >>
  simp[] >> qexistsl_tac [`slot`, `tv'`] >> gvs[]
QED

Theorem store_copy_region_dead_elim[local]:
  storage_dead H tr st j b /\ MEM (tr,k,tv) (FST H) /\
  w2n k <= j /\ j < w2n k + type_slot_size tv ==>
  dead_bytes st (w2n k) tv j b
Proof
  pure_rewrite_tac[storage_dead_def] >>
  disch_then (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 kall_tac strip_assume_tac) strip_assume_tac) >>
  Cases_on `(slot,tv') = (k,tv)` >- gvs[] >>
  `ranges_disjoint (w2n slot) (type_slot_size tv') (w2n k) (type_slot_size tv)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  drule (cj 1 dead_bytes_range) >>
  fs[vyperStorageFrameTheory.ranges_disjoint_def]
QED

Theorem store_copy_live_storage_dead:
  declared_storage_region cx mid n subs = SOME (tr,k,tv) /\
  MEM (tr,k,tv) (FST H) /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  well_formed_type_value tv /\ value_has_type tv v /\
  encode_value tv v = SOME writes /\
  w2n k + type_slot_size tv <= dimword (:256) /\
  (!m. mem_agree_outside ta mem m ==> val_in_memory tv v off m) /\
  (!i c. w2n k <= i /\ i < w2n k + type_slot_size tv /\ c < 32 /\
     ~dead_bytes (apply_writes k writes st) (w2n k) tv i c ==>
     EL c (word_to_bytes (lookup_storage (n2w i) final) T) =
     EL c (word_to_bytes (lookup_storage (n2w i)
       (apply_writes k writes st)) T)) /\
  (!i. i < dimword (:256) /\
       ~(w2n k <= i /\ i < w2n k + type_slot_size tv) ==>
       lookup_storage (n2w i) final = lookup_storage (n2w i) st) /\
  (!q b. (q,b) IN old ==> storage_dead H tr st (w2n q) b) /\
  new SUBSET (old DIFF {(k+n2w i,b) | (i,b) | MEM i (MAP FST writes)}) UNION
    {(k+n2w i,b) | MEM i (MAP FST writes) /\ b<32 /\ off+32*i+b IN ta} ==>
  !q b. (q,b) IN new ==> storage_dead H tr final (w2n q) b
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `new SUBSET _` mp_tac >>
  simp[SUBSET_DEF] >> disch_then drule >>
  simp[] >> strip_tac
  >- (Cases_on `w2n k <= w2n q /\ w2n q < w2n k + type_slot_size tv`
      >- (`~MEM (w2n q - w2n k) (MAP FST writes)` by
            (strip_tac >>
             `k + n2w (w2n q - w2n k) = q` by
               (simp[n2w_sub, GSYM WORD_ADD_SUB_ASSOC, WORD_ADD_SUB2]) >>
             metis_tac[]) >>
          `dead_bytes st (w2n k) tv (w2n q) b` by
            (irule store_copy_region_dead_elim >> metis_tac[]) >>
          `dead_bytes (apply_writes k writes st) (w2n k) tv (w2n q) b` by
            (drule (cj 1 dead_bytes_range) >> strip_tac >>
             `w2n k + (w2n q - w2n k) = w2n q` by decide_tac >>
             mp_tac (Q.SPECL [`tv`,`v`,`writes`,`st`,`w2n (k:bytes32)`,
               `w2n (q:bytes32) - w2n (k:bytes32)`,`b`]
               place_store_unwritten_live_preserved) >>
             simp[] >> metis_tac[]) >>
          irule declared_region_dead_at_endpoint >>
          metis_tac[]) >>
      irule storage_dead_endpoint_outside >> metis_tac[]) >>
  rename1 `MEM i (MAP FST writes)` >>
  `i < type_slot_size tv` by metis_tac[encode_writes_bounded] >>
  `w2n (k + n2w i) = w2n k + i` by
    (`w2n k + i < dimword (:256)` by decide_tac >>
     `i < dimword (:256)` by decide_tac >> simp[w2n_add_2, w2n_n2w]) >>
  `off + 32*i + b IN ta` by
    (`off + 32*i + b = b + (32*i + off)` by decide_tac >>
     asm_rewrite_tac[]) >>
  drule_all robust_memory_storage_dead_at_endpoint >> asm_rewrite_tac[]
QED

Theorem store_copy_live_stor_taint_ok:
  declared_storage_region cx mid n subs = SOME (tr,k,tv) /\
  MEM (tr,k,tv) (FST H) /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  well_formed_type_value tv /\ value_has_type tv v /\
  encode_value tv v = SOME writes /\
  w2n k + type_slot_size tv <= dimword (:256) /\
  (!m. mem_agree_outside ta mem m ==> val_in_memory tv v off m) /\
  st = (if tr then s.vs_transient s.vs_call_ctx.cc_address
        else (s.vs_accounts s.vs_call_ctx.cc_address).storage) /\
  final = (if tr then u.vs_transient u.vs_call_ctx.cc_address
           else (u.vs_accounts u.vs_call_ctx.cc_address).storage) /\
  (!i c. w2n k <= i /\ i < w2n k + type_slot_size tv /\ c < 32 /\
     ~dead_bytes (apply_writes k writes st) (w2n k) tv i c ==>
     EL c (word_to_bytes (lookup_storage (n2w i) final) T) =
     EL c (word_to_bytes (lookup_storage (n2w i)
       (apply_writes k writes st)) T)) /\
  (!i. i < dimword (:256) /\
       ~(w2n k <= i /\ i < w2n k + type_slot_size tv) ==>
       lookup_storage (n2w i) final = lookup_storage (n2w i) st) /\
  stor_taint_ok H cx tn s /\
  u.vs_call_ctx.cc_address = cx.txn.target /\
  u.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
  tf.t_imm = tn.t_imm /\
  (if tr then tf.t_stor = tn.t_stor /\
     (u.vs_accounts u.vs_call_ctx.cc_address).storage =
     (s.vs_accounts s.vs_call_ctx.cc_address).storage
   else tf.t_trans = tn.t_trans /\
     u.vs_transient u.vs_call_ctx.cc_address =
     s.vs_transient s.vs_call_ctx.cc_address) /\
  (if tr then tf.t_trans else tf.t_stor) SUBSET
    ((if tr then tn.t_trans else tn.t_stor) DIFF
       {(k+n2w i,b) | (i,b) | MEM i (MAP FST writes)}) UNION
    {(k+n2w i,b) | MEM i (MAP FST writes) /\ b<32 /\ off+32*i+b IN ta} ==>
  stor_taint_ok H cx tf u
Proof
  strip_tac >>
  `!q b. (q,b) IN (if tr then tn.t_trans else tn.t_stor) ==>
     storage_dead H tr st (w2n q) b` by
    (Cases_on `tr` >>
     fs[bodyPtrDefsTheory.stor_taint_ok_def,
        sourceUnitExecutionTheory.cx_dead_def, SUBSET_DEF,
        pairTheory.FORALL_PROD] >> metis_tac[]) >>
  `!q b. (q,b) IN (if tr then tf.t_trans else tf.t_stor) ==>
     storage_dead H tr final (w2n q) b` by
    (rpt strip_tac >> drule_all store_copy_live_storage_dead >> simp[]) >>
  irule stor_taint_ok_selected_space >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`s`, `tn`, `tr`] >> asm_rewrite_tac[] >>
  metis_tac[]
QED
