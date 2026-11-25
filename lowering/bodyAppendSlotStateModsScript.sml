(* Fixed-endpoint state relation and storage well-formedness for slot Append. *)
Theory bodyAppendSlotStateMods
Ancestors
  bodySlotCopyStateMods bodyFullAppendNestedFrames bodyPtrDefs
  placeStoreStorage stmtSimStoreCopy loweringStateRelDefs stmtSimAssignStorageCopy
  vyperStoragePlaceObserved vyperStoragePlaceRegion vyperStorageBackend
  vyperFiniteStoragePreservation vyperStorageFootprint vyperEncodeDecode
  vyperStorage vyperValue vyperTyping vfmState venomState words list

Theorem append_slot_state_layout[local]:
  storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) /\
  regions_consistent (FST H) ==>
  w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
  ?rootk root path delta.
    MEM (tr,rootk,root) (FST H) /\
    storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
    w2n slot = w2n rootk + delta /\
    w2n rootk + type_slot_size root <= dimword (:256)
Proof
  simp[storage_place_observed_def] >> strip_tac >> gvs[] >>
  drule_all_then strip_assume_tac place_store_root_layout >>
  drule_then assume_tac storage_subregion_bounds >>
  `0 < type_slot_size (ArrayTV tv (Dynamic cap))` by simp[type_slot_size_def] >>
  `delta < dimword (:256) /\ w2n root + delta < dimword (:256)` by decide_tac >>
  `w2n (root + n2w delta) = w2n root + delta` by
    simp[word_add_def, w2n_n2w, arithmeticTheory.LESS_MOD] >>
  conj_tac >- decide_tac >> qexistsl_tac [`root`, `tv'`, `path`, `delta`] >>
  asm_rewrite_tac[] >> decide_tac
QED

Theorem append_slot_state_fold_frame[local]:
  !ks s z.
    let t = FOLDL (\q i. (if tr then tstore else sstore) (k+n2w i)
                            (mload (off+32*i) s) q) z ks in
    store_copy_normalize s t =
      FOLDL (\q i. (if tr then tstore else sstore) (k+n2w i)
                    (mload (off+32*i) s) q) (store_copy_normalize s z) ks /\
    !x. lookup_var x t = lookup_var x z
Proof
  Induct >> simp[] >> rpt gen_tac >>
  first_x_assum (qspecl_then [`s`, `(if tr then tstore else sstore) (k+n2w h)
                                     (mload (off+32*h) s) z`] strip_assume_tac) >>
  Cases_on `tr` >>
  gvs[store_copy_normalize_def, tstore_def, sstore_def, lookup_var_def]
QED

Theorem append_slot_state_header[local]:
  stmt_state_rel H ctx func cenv cx (set_storage cx es tr raw) t /\
  MEM (tr,rootk,root) (FST H) /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
  w2n slot = w2n rootk + delta ==>
  stmt_state_rel H ctx func cenv cx (set_storage cx es tr (update_storage slot h raw))
    ((if tr then tstore else sstore) slot h t)
Proof
  strip_tac >>
  `!j b. storage_dead H tr (update_storage slot h raw) j b <=> storage_dead H tr raw j b` by
    (rpt gen_tac >> irule append_subregion_header_storage_dead >> asm_rewrite_tac[] >>
     qexistsl_tac [`cap`, `delta`, `path`, `root`, `rootk`, `tv`] >> asm_rewrite_tac[]) >>
  drule_then (qspec_then `tr` assume_tac) storage_copy_initial_agree >>
  qpat_x_assum `storage_agree _ _ _` mp_tac >> simp[get_storage_after_set] >>
  qabbrev_tac `low = if tr then contract_transient t else contract_storage t` >>
  strip_tac >>
  `storage_agree (storage_dead H tr (update_storage slot h raw))
     (update_storage slot h raw) (update_storage slot h low)` by
    (fs[storage_agree_def] >> rpt strip_tac >> rename1 `lookup_storage q _` >>
     Cases_on `q = slot` >>
     gvs[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM]) >>
  drule_all (INST_TYPE [alpha |-> ``:256``] place_store_storage_replace) >>
  Cases_on `tr` >>
  simp[Abbr `low`, set_storage_def, tstore_def, sstore_def, contract_transient_def,
       contract_storage_def, lookup_account_def, combinTheory.APPLY_UPDATE_THM,
       combinTheory.UPDATE_EQ]
QED

Theorem append_slot_state_wf_mods:
  stmt_state_rel H ctx func cenv cx es s /\
  storage_well_formed_on cx es (FST H) /\
  storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) /\
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  len < cap /\ cap < dimword (:256) /\
  k = slot+n2w (1+len*type_slot_size tv) /\
  well_formed_type_value tv /\ value_has_type tv v /\ encode_value tv v = SOME writes /\
  (!mem. mem_agree_outside M s.vs_memory mem ==> val_in_memory tv v off mem) /\
  (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
  store_copy_normalize s u =
    (if tr then tstore else sstore) slot (n2w (len+1))
      (FOLDL (\q i. (if tr then tstore else sstore) (k+n2w i)
                    (mload (off+32*i) s) q) s ks) /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v es = (INL (),ef) /\
  ef = set_storage cx es tr
         (update_storage slot (n2w (len+1)) (apply_writes k writes (get_storage cx es tr))) ==>
  stmt_state_rel H ctx func cenv cx ef u /\ storage_well_formed_on cx ef (FST H)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac append_slot_state_layout >>
  reverse conj_tac
  >- (`well_formed_type_value (ArrayTV tv (Dynamic cap))` by
        (simp[well_formed_type_value_def] >> decide_tac) >>
      drule_all_then ACCEPT_TAC append_subregion_preserves_storage_well_formed_on) >>
  qabbrev_tac `t = FOLDL (\q i. (if tr then tstore else sstore) (k+n2w i)
                                (mload (off+32*i) s) q) s ks` >>
  `stmt_state_rel H ctx func cenv cx
     (set_storage cx es tr (apply_writes k writes (get_storage cx es tr))) t` by
    suspend "payload" >>
  irule place_store_normalized_stmt_state >> qexistsl_tac [`s`, `sa`] >> simp[] >>
  qpat_assum `ef = _` SUBST1_TAC >> qpat_assum `store_copy_normalize s u = _` SUBST1_TAC >>
  irule append_slot_state_header >> asm_rewrite_tac[] >>
  reverse conj_tac
  >- (`len * type_slot_size tv + 1 = 1 + len * type_slot_size tv` by decide_tac >>
      pop_assum (fn th => pure_rewrite_tac[th]) >>
      qpat_assum `k = _` (fn th => pure_rewrite_tac[GSYM th]) >>
      first_assum ACCEPT_TAC) >>
  qexistsl_tac [`cap`, `delta`, `path`, `root`, `rootk`, `tv`] >> simp[]
QED

Resume append_slot_state_wf_mods[payload]:
  Cases_on `type_slot_size tv = 0`
  >- (`!i. ~MEM i (MAP FST writes)` by
        metis_tac[cj 1 encode_writes_bounded, prim_recTheory.NOT_LESS_0] >>
      `writes = []` by
        (Cases_on `writes` >> simp[] >>
         qpat_x_assum `!i. ~MEM i (MAP FST _)` mp_tac >> simp[] >> metis_tac[]) >>
      `ks = []` by
        (Cases_on `ks` >> simp[] >>
         qpat_x_assum `!i. MEM i (_::_) <=> _` mp_tac >> simp[] >> metis_tac[]) >>
      Cases_on `tr` >>
      simp[Abbr `t`, apply_writes_def, set_storage_def, get_storage_def,
           place_store_update_identity]) >>
  `0 < type_slot_size tv` by decide_tac >>
  drule_all_then strip_assume_tac append_observed_child >>
  `val_in_memory tv v off s.vs_memory` by fs[mem_agree_outside_def] >>
  `store_copy_normalize s t = t /\ (!x. lookup_var x t = lookup_var x s)` by
    (simp_tac bool_ss [Abbr `t`, SIMP_RULE bool_ss [LET_THM] append_slot_state_fold_frame] >>
     simp[store_copy_normalize_def]) >>
  irule slot_copy_sparse_state_mods >> asm_rewrite_tac[] >>
  qexistsl_tac [`delta + (1+len*type_slot_size tv)`, `ks`, `off`,
                `path ++ [ValueSubscript (IntV (&len))]`, `root`, `rootk`,
                `s`, `sa`, `tv`, `v`] >>
  simp[Abbr `t`]
QED

Finalise append_slot_state_wf_mods
