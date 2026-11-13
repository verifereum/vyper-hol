Theory appendStorageAggregateRel
Ancestors
  appendStorageRel storageCopyLive placeStoreSlots
  stmtSimStoreCopyState
  stmtSimAppendStorage stmtSimStoreCopy bodyMemAssignTopCopySem
  stmtSimDefs stmtSimProps exprSimProps exprLoweringProps
  accountsRelProps loweringStateRelDefs vyperStorageFrame vyperStorageBackend
  vyperEncodeDecode vyperStorage vyperValue words vyperState vfmState venomState

Theorem append_storage_aggregate_source[local]:
  ~cx.txn.is_static /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\ len < cap /\
  encode_value tv v = SOME writes ==>
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es =
  (INL (), set_storage cx es tr
    (update_storage slot (n2w (len+1))
      (apply_writes (slot+n2w (1+len*type_slot_size tv)) writes
        (get_storage cx es tr))))
Proof
  strip_tac >>
  simp[append_storage_writes, ignore_bind_def, bind_def,
       write_storage_slot_eq, get_storage_after_set,
       encode_value_def, encode_base_to_slot_def, apply_writes_def,
       integer_wordTheory.i2w_def] >>
  Cases_on `tr` >>
  simp[set_storage_def, update_account_def, vfmStateTheory.lookup_account_def,
       combinTheory.APPLY_UPDATE_THM]
QED

Theorem append_aggregate_header_dead[local]:
  w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) ==>
  (dead_bytes (update_storage slot h st) (w2n slot)
     (ArrayTV tv (Dynamic cap)) j b <=>
   dead_bytes st (w2n slot) (ArrayTV tv (Dynamic cap)) j b)
Proof
  strip_tac >> simp[Once dead_bytes_def] >>
  `!i. i < cap ==>
    (dead_bytes (update_storage slot h st)
       (w2n slot + 1 + i * type_slot_size tv) tv j b <=>
     dead_bytes st (w2n slot + 1 + i * type_slot_size tv) tv j b)` by
    (rpt strip_tac >> irule (cj 1 dead_bytes_frame) >>
     rpt strip_tac >> simp[lookup_storage_def, update_storage_def] >>
     `i' < dimword (:256)` by
       (gvs[type_slot_size_def] >>
        `i * type_slot_size tv + type_slot_size tv <= cap * type_slot_size tv` by
          (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
        decide_tac) >>
     `n2w i' <> slot` by
       (strip_tac >> `i' = w2n slot` by metis_tac[w2n_n2w, arithmeticTheory.LESS_MOD] >> decide_tac) >>
     simp[combinTheory.APPLY_UPDATE_THM]) >>
  pure_rewrite_tac[dead_bytes_def] >>
  `!i. w2n slot + (i * type_slot_size tv + 1) =
       w2n slot + 1 + i * type_slot_size tv` by (gen_tac >> decide_tac) >>
  metis_tac[]
QED

Theorem append_aggregate_header_storage_dead[local]:
  declared_storage_region cx mid name [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
  (!mid' n' subs' slot' tv'.
    declared_storage_region cx mid' n' subs' = SOME (tr,slot',tv') /\
    (slot',tv') <> (slot,ArrayTV tv (Dynamic cap)) ==>
    ranges_disjoint (w2n slot) (type_slot_size (ArrayTV tv (Dynamic cap)))
                    (w2n slot') (type_slot_size tv')) ==>
  (storage_dead cx tr (update_storage slot h st) j b <=> storage_dead cx tr st j b)
Proof
  strip_tac >>
  `storage_dead cx tr (update_storage slot h st) = storage_dead cx tr st`
    suffices_by simp[] >>
  irule storage_dead_update_in_region >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  simp[type_slot_size_def] >> rpt gen_tac >>
  irule append_aggregate_header_dead >> simp[]
QED

Theorem append_aggregate_header_agree[local]:
  declared_storage_region cx mid name [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
  (!mid' n' subs' slot' tv'.
    declared_storage_region cx mid' n' subs' = SOME (tr,slot',tv') /\
    (slot',tv') <> (slot,ArrayTV tv (Dynamic cap)) ==>
    ranges_disjoint (w2n slot) (type_slot_size (ArrayTV tv (Dynamic cap)))
                    (w2n slot') (type_slot_size tv')) /\
  storage_agree (storage_dead cx tr st) st mt ==>
  storage_agree (storage_dead cx tr (update_storage slot h st))
    (update_storage slot h st) (update_storage slot h mt)
Proof
  strip_tac >>
  `!j b. storage_dead cx tr (update_storage slot h st) j b <=>
         storage_dead cx tr st j b` by
    (rpt gen_tac >> irule append_aggregate_header_storage_dead >>
     qexistsl_tac [`cap`, `mid`, `name`, `tv`] >> metis_tac[]) >>
  fs[storage_agree_def] >> rpt strip_tac >>
  Cases_on `k = slot` >>
  gvs[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

(* The reusable fold in assignBasePtrStorageSemantic currently imports the
   constSubstCorrect red cone; keep this field calculation local. *)
Theorem assign_base_store_backend_fold[local]:
  !is k ws s tr.
    FOLDL (\t i. (if tr then tstore else sstore) (k+n2w i) (ws i) t) s is =
    if tr then
      s with vs_transient :=
        (s.vs_call_ctx.cc_address =+
          FOLDL (\t i. update_storage (k+n2w i) (ws i) t)
            (contract_transient s) is) s.vs_transient
    else
      s with vs_accounts :=
        (s.vs_call_ctx.cc_address =+
          (lookup_account s.vs_call_ctx.cc_address s.vs_accounts with storage :=
            FOLDL (\t i. update_storage (k+n2w i) (ws i) t)
              (contract_storage s) is)) s.vs_accounts
Proof
  Induct >> rpt gen_tac >> Cases_on `tr` >>
  simp[listTheory.FOLDL, sstore_def, tstore_def, contract_storage_def,
       contract_transient_def, vfmStateTheory.lookup_account_def,
       combinTheory.APPLY_UPDATE_THM, combinTheory.APPLY_UPDATE_ID]
QED

Theorem append_aggregate_accounts_fold[local]:
  accounts_rel cx es s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
  storage_agree (storage_dead cx tr stor) stor
    (update_storage slot h (FOLDL (\t i. update_storage (a+n2w i) (ws i) t)
      (if tr then contract_transient s else contract_storage s) is)) ==>
  accounts_rel cx (set_storage cx es tr stor)
    ((if tr then tstore else sstore) slot h
      (FOLDL (\t i. (if tr then tstore else sstore) (a+n2w i) (ws i) t) s is))
Proof
  strip_tac >> simp[assign_base_store_backend_fold] >> Cases_on `tr` >> gvs[]
  >- (irule accounts_rel_set_transient >>
      qexistsl_tac [`es`, `s`, `stor`] >>
      simp[set_storage_backend_eq, tstore_def, contract_transient_def,
           update_storage_def, combinTheory.APPLY_UPDATE_THM] >>
      goal_assum (drule_at Any) >>
      simp[contract_transient_def, contract_storage_def, update_storage_def,
           vfmStateTheory.lookup_account_def]) >>
  irule accounts_rel_set_storage >>
  qexistsl_tac [`es`, `s`, `stor`] >>
  simp[set_storage_backend_eq, sstore_def, contract_storage_def,
       vfmStateTheory.lookup_account_def, update_storage_def, combinTheory.APPLY_UPDATE_THM] >>
  goal_assum (drule_at Any) >>
      simp[contract_transient_def, contract_storage_def, update_storage_def,
           vfmStateTheory.lookup_account_def]
QED

Theorem append_aggregate_state_fold[local]:
  stmt_state_rel ctx func cenv cx es s /\
  storage_agree (storage_dead cx tr stor) stor
    (update_storage slot h (FOLDL (\t i. update_storage (a+n2w i) (ws i) t)
      (if tr then contract_transient s else contract_storage s) is)) ==>
  stmt_state_rel ctx func cenv cx (set_storage cx es tr stor)
    ((if tr then tstore else sstore) slot h
      (FOLDL (\t i. (if tr then tstore else sstore) (a+n2w i) (ws i) t) s is))
Proof
  strip_tac >>
  `s.vs_call_ctx.cc_address = cx.txn.target /\ accounts_rel cx es s` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  drule_all append_aggregate_accounts_fold >> strip_tac >>
  qmatch_asmsub_abbrev_tac `accounts_rel cx es1 s1` >>
  drule accounts_rel_storage_transient >> strip_tac >>
  `state_rel func cenv cx es1 s1` by
    (Cases_on `tr` >> gvs[Abbr `s1`, Abbr `es1`, assign_base_store_backend_fold] >>
     fs[stmt_state_rel_def, state_rel_def, set_storage_def, sstore_def, tstore_def,
        local_ptrs_rel_def, local_backed_def, local_region_def, lookup_var_def,
        immutables_rel_def, logs_rel_def] >> gvs[] >> metis_tac[]) >>
  `immutable_alloca_sep func cenv cx es1 s1` by
    (`immutable_alloca_sep func cenv cx es s` by fs[stmt_state_rel_def] >>
     irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >>
     simp[] >> Cases_on `tr` >>
     simp[Abbr `s1`, Abbr `es1`, assign_base_store_backend_fold, sstore_def, tstore_def,
          set_storage_def, local_region_def, lookup_var_def] >> metis_tac[]) >>
  `immutable_base_zero cenv s1` by
    (`immutable_base_zero cenv s` by fs[stmt_state_rel_def] >>
     irule immutable_base_zero_frame >> qexists_tac `s` >>
     Cases_on `tr` >> simp[Abbr `s1`, assign_base_store_backend_fold, sstore_def, tstore_def, lookup_var_def]) >>
  irule stmt_state_rel_allocas_frame >>
  qpat_assum `immutable_base_zero cenv _` (irule_at Any) >> simp[] >>
  qexistsl_tac [`s`, `es`] >> simp[] >> Cases_on `tr` >>
  simp[Abbr `s1`, assign_base_store_backend_fold, sstore_def, tstore_def]
QED

Theorem append_sparse_agree_at_word[local]:
  !cx tr mid name subs rootk root path delta tv k writes v ks rd st1 st2.
    declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
    storage_subregion root path delta tv /\
    w2n k = w2n rootk + delta /\ 0 < type_slot_size tv /\
    w2n rootk + type_slot_size root <= dimword (:256) /\
    (!mid' name' subs' k' tv'.
       declared_storage_region cx mid' name' subs' = SOME (tr,k',tv') /\
       (k',tv') <> (rootk,root) ==>
       ranges_disjoint (w2n rootk) (type_slot_size root)
                       (w2n k') (type_slot_size tv')) /\
    encode_value tv v = SOME writes /\ value_has_type tv v /\
    w2n k + type_slot_size tv <= dimword (:256) /\
    (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
    (!i b. i < type_slot_size tv /\ b < 32 /\ MEM i (MAP FST writes) /\
       ~dead_bytes (apply_writes k writes st1) (w2n k) tv (w2n k+i) b ==>
       EL b (word_to_bytes (lookup_storage (k+n2w i)
         (apply_writes k writes st1)) T) =
       EL b (word_to_bytes (rd i) T)) /\
    storage_agree (storage_dead cx tr st1) st1 st2 ==>
    storage_agree (storage_dead cx tr (apply_writes k writes st1))
      (apply_writes k writes st1)
      (FOLDL (\st i. update_storage (k+n2w i) (rd i) st) st2 ks)
Proof
  rpt gen_tac >> strip_tac >>
  `storage_agree
     (storage_dead cx tr (apply_writes (n2w (w2n k)) writes st1))
     (apply_writes (n2w (w2n k)) writes st1)
     (FOLDL (\st i. update_storage (n2w (w2n k+i)) (rd i) st) st2 ks)` by
    (irule place_store_encoded_copy_agree_sparse >>
     simp[GSYM wordsTheory.word_add_n2w] >>
     qexistsl_tac [`delta`, `mid`, `name`, `path`, `root`, `rootk`, `subs`, `tv`, `v`] >>
     simp[] >> metis_tac[pairTheory.PAIR_EQ]) >>
  gvs[GSYM wordsTheory.word_add_n2w]
QED

Theorem stmt_state_rel_append_storage_aggregate:
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid name [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
  (!mid' n' subs' slot' tv'.
    declared_storage_region cx mid' n' subs' = SOME (tr,slot',tv') /\
    (slot',tv') <> (slot,ArrayTV tv (Dynamic cap)) ==>
    ranges_disjoint (w2n slot) (type_slot_size (ArrayTV tv (Dynamic cap)))
                    (w2n slot') (type_slot_size tv')) /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\ len < cap /\
  0 < type_slot_size tv /\ well_formed_type_value tv /\ value_has_type tv v /\
  val_in_memory tv v off s.vs_memory /\ encode_value tv v = SOME writes /\
  (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es = (res,es') ==>
  res = INL () /\
  stmt_state_rel ctx func cenv cx es'
    ((if tr then tstore else sstore) slot (n2w (len+1))
      (FOLDL (\t i. (if tr then tstore else sstore)
        (slot+n2w (1+len*type_slot_size tv)+n2w i)
        (mem_word_at (off+32*i) s.vs_memory) t) s ks))
Proof
  strip_tac >>
  `cap <= cap*type_slot_size tv` by
    (Cases_on `type_slot_size tv` >> gvs[arithmeticTheory.MULT_CLAUSES]) >>
  `len+1 < dimword (:256)` by
    (qpat_x_assum `w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= _` mp_tac >>
     simp_tac (srw_ss()) [type_slot_size_def] >> decide_tac) >>
  `len*type_slot_size tv+type_slot_size tv <= cap*type_slot_size tv` by
    (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  `w2n (slot+n2w (1+len*type_slot_size tv)) = w2n slot+1+len*type_slot_size tv` by
    (`w2n slot+(1+len*type_slot_size tv) < dimword (:256)` by
       (gvs[type_slot_size_def] >> decide_tac) >>
     gvs[type_slot_size_def, w2n_add_2]) >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all append_storage_aggregate_source >> strip_tac >> gvs[] >>
  ho_match_mp_tac append_aggregate_state_fold >> simp[] >>
  irule append_aggregate_header_agree >>
  conj_tac
  >- (qexistsl_tac [`cap`, `mid`, `name`, `tv`] >>
      metis_tac[arithmeticTheory.ADD_COMM, pairTheory.PAIR_EQ]) >>
  (qmatch_goalsub_abbrev_tac `apply_writes dst writes _` >>
   ho_match_mp_tac append_sparse_agree_at_word >>
      goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
      qexistsl_tac [`[ValueSubscript (IntV (&w2n (lookup_storage slot (get_storage cx es tr))))]`,
        `1 + w2n (lookup_storage slot (get_storage cx es tr)) * type_slot_size tv`, `tv`, `v`] >>
      simp[vyperStoragePlaceRegionTheory.storage_subregion_def] >>
      conj_tac >- metis_tac[] >>
      conj_asm1_tac
      >- (gvs[type_slot_size_def] >> decide_tac) >>
      reverse conj_tac >- metis_tac[stmt_state_selected_storage_agree] >>
      rpt strip_tac >>
      `w2n dst < dimword (:256)` by simp[] >>
      `EL b (word_to_bytes
          (lookup_storage (n2w (w2n dst+i))
            (apply_writes (n2w (w2n dst)) writes (get_storage cx es tr))) T) =
       EL b (word_to_bytes (mload (off+32*i) s) T)` suffices_by
        simp[GSYM wordsTheory.word_add_n2w,
             valueEncodingPropsTheory.mem_word_at_eq_mload] >>
      irule placeStoreStorageTheory.place_store_memory_live_at >>
      simp[GSYM wordsTheory.word_add_n2w] >>
      metis_tac[arithmeticTheory.ADD_COMM]) >>
  metis_tac[]
QED
