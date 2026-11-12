Theory appendStorageAggregateRel
Ancestors
  appendStorageRel storageCopyLive
  stmtSimAppendStorage stmtSimStoreCopy vyperStorageFootprint
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

Theorem append_aggregate_backend_fold[local]:
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
  simp[FOLDL, sstore_def, tstore_def, contract_storage_def,
       contract_transient_def, vfmStateTheory.lookup_account_def,
       combinTheory.APPLY_UPDATE_THM, combinTheory.APPLY_UPDATE_ID]
QED

Theorem append_aggregate_accounts_fold[local]:
  accounts_rel H cx es s /\ s.vs_call_ctx.cc_address = cx.txn.target /\
  storage_agree (storage_dead H tr stor) stor
    (update_storage slot h (FOLDL (\t i. update_storage (a+n2w i) (ws i) t)
      (if tr then contract_transient s else contract_storage s) is)) ==>
  accounts_rel H cx (set_storage cx es tr stor)
    ((if tr then tstore else sstore) slot h
      (FOLDL (\t i. (if tr then tstore else sstore) (a+n2w i) (ws i) t) s is))
Proof
  strip_tac >> simp[append_aggregate_backend_fold] >> Cases_on `tr` >> gvs[]
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
  stmt_state_rel H ctx func cenv cx es s /\
  storage_agree (storage_dead H tr stor) stor
    (update_storage slot h (FOLDL (\t i. update_storage (a+n2w i) (ws i) t)
      (if tr then contract_transient s else contract_storage s) is)) ==>
  stmt_state_rel H ctx func cenv cx (set_storage cx es tr stor)
    ((if tr then tstore else sstore) slot h
      (FOLDL (\t i. (if tr then tstore else sstore) (a+n2w i) (ws i) t) s is))
Proof
  strip_tac >>
  `s.vs_call_ctx.cc_address = cx.txn.target /\ accounts_rel H cx es s` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  drule_all append_aggregate_accounts_fold >> strip_tac >>
  qmatch_asmsub_abbrev_tac `accounts_rel H cx es1 s1` >>
  drule accounts_rel_storage_transient >> strip_tac >>
  `state_rel H func cenv cx es1 s1` by
    (Cases_on `tr` >> gvs[Abbr `s1`, Abbr `es1`, append_aggregate_backend_fold] >>
     fs[stmt_state_rel_def, state_rel_def, set_storage_def, sstore_def, tstore_def,
        local_ptrs_rel_def, local_backed_def, local_region_def, lookup_var_def,
        immutables_rel_def, logs_rel_def] >> gvs[] >> metis_tac[]) >>
  `immutable_alloca_sep func cenv cx es1 s1` by
    (`immutable_alloca_sep func cenv cx es s` by fs[stmt_state_rel_def] >>
     irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >>
     simp[] >> Cases_on `tr` >>
     simp[Abbr `s1`, Abbr `es1`, append_aggregate_backend_fold, sstore_def, tstore_def,
          set_storage_def, local_region_def, lookup_var_def] >> metis_tac[]) >>
  `immutable_base_zero cenv s1` by
    (`immutable_base_zero cenv s` by fs[stmt_state_rel_def] >>
     irule immutable_base_zero_frame >> qexists_tac `s` >>
     Cases_on `tr` >> simp[Abbr `s1`, append_aggregate_backend_fold, sstore_def, tstore_def, lookup_var_def]) >>
  irule stmt_state_rel_allocas_frame >>
  qpat_assum `immutable_base_zero cenv _` (irule_at Any) >> simp[] >>
  qexistsl_tac [`s`, `es`] >> simp[] >> Cases_on `tr` >>
  simp[Abbr `s1`, append_aggregate_backend_fold, sstore_def, tstore_def]
QED

Theorem stmt_state_rel_append_storage_aggregate:
  stmt_state_rel H ctx func cenv cx es s /\
  MEM (tr,slot,ArrayTV tv (Dynamic cap)) (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
  (!slot' tv'.
    MEM (tr,slot',tv') (FST H) /\
    (slot',tv') <> (slot,ArrayTV tv (Dynamic cap)) ==>
    ranges_disjoint (w2n slot) (type_slot_size (ArrayTV tv (Dynamic cap)))
                    (w2n slot') (type_slot_size tv')) /\
  len = w2n (lookup_storage slot (get_storage cx es tr)) /\ len < cap /\
  0 < type_slot_size tv /\ well_formed_type_value tv /\ value_has_type tv v /\
  val_in_memory tv v off s.vs_memory /\ encode_value tv v = SOME writes /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es = (res,es') ==>
  res = INL () /\
  stmt_state_rel H ctx func cenv cx es'
    ((if tr then tstore else sstore) slot (n2w (len+1))
      (FOLDL (\t i. (if tr then tstore else sstore)
        (slot+n2w (1+len*type_slot_size tv)+n2w i)
        (mem_word_at (off+32*i) s.vs_memory) t) s (COUNT_LIST (type_slot_size tv))))
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
     simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w,
          arithmeticTheory.LESS_MOD]) >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all append_storage_aggregate_source >> strip_tac >> gvs[] >>
  ho_match_mp_tac append_aggregate_state_fold >> simp[] >>
  `storage_rel H cx.txn.target es s /\ transient_rel H cx.txn.target es s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `storage_agree (storage_dead H tr (get_storage cx es tr))
    (get_storage cx es tr) (if tr then contract_transient s else contract_storage s)` by
    (Cases_on `tr` >>
     gvs[storage_rel_def, transient_rel_def, get_storage_def,
         vfmStateTheory.lookup_account_def]) >>
  qspecl_then [`H`, `tr`, `slot`, `tv`, `cap`,
    `w2n (lookup_storage slot (get_storage cx es tr))`,
    `slot+n2w (1+w2n (lookup_storage slot (get_storage cx es tr))*type_slot_size tv)`,
    `v`, `writes`, `off`, `s.vs_memory`, `get_storage cx es tr`,
    `if tr then contract_transient s else contract_storage s`] mp_tac
    append_storage_agree_copy >>
  impl_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  simp[]
QED
