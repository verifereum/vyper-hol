(* The source-state effect of a counted sparse slot copy. *)
Theory bodySlotCopyStateMods
Ancestors
  placeStoreStorage placeStoreSlots loweringStateRelDefs stateRelProj
  stateRelProjStorage vyperStorageFootprint vyperStoragePlaceObserved
  vyperFiniteStoragePreservation vyperStoragePlaceRegion vyperStorageBackend
  vyperStorage vyperStorageFrame vyperState vyperTypeInvariants vyperTyping
  bodyFullStoreSlotsFrame bodyMemoryDefs venomState list words

Theorem slot_copy_initial_bank_agree[local]:
  stmt_state_rel H ctx func cenv cx ee s ==>
  storage_agree (storage_dead H tr (get_storage cx ee tr))
    (get_storage cx ee tr)
    (if tr then contract_transient s else contract_storage s)
Proof
  strip_tac >> drule_then assume_tac stmt_state_rel_state_rel >>
  Cases_on `tr`
  >- (drule_then mp_tac state_rel_transient_rel >>
      simp[transient_rel_def, get_storage_def]) >>
  drule_then mp_tac state_rel_storage_rel >>
  simp[storage_rel_def, get_storage_def, vfmStateTheory.lookup_account_def]
QED

Theorem slot_copy_fold_bank[local]:
  !ks z.
    FOLDL (\q i. (if tr then tstore else sstore) (k+n2w i) (mload (32*i+off) s) q) z ks =
    if tr then z with vs_transient :=
      (z.vs_call_ctx.cc_address =+
         FOLDL (\st i. update_storage (k+n2w i) (mload (32*i+off) s) st)
           (contract_transient z) ks) z.vs_transient
    else z with vs_accounts :=
      (z.vs_call_ctx.cc_address =+
         (vfmState$lookup_account z.vs_call_ctx.cc_address z.vs_accounts with storage :=
          FOLDL (\st i. update_storage (k+n2w i) (mload (32*i+off) s) st)
            (contract_storage z) ks)) z.vs_accounts
Proof
  Induct
  >- (gen_tac >> Cases_on `tr` >>
      simp[FOLDL, contract_storage_def, contract_transient_def,
           vfmStateTheory.lookup_account_def, place_store_update_identity]) >>
  map_every qx_gen_tac [`h`, `acc`] >> once_rewrite_tac[FOLDL] >>
  first_x_assum (qspec_then `(if tr then tstore else sstore) (k+n2w h) (mload (32*h+off) s) acc` mp_tac) >>
  Cases_on `tr` >>
  simp[sstore_def, tstore_def, contract_storage_def, contract_transient_def,
       vfmStateTheory.lookup_account_def, combinTheory.APPLY_UPDATE_THM,
       combinTheory.UPDATE_EQ]
QED

Theorem slot_copy_sparse_state_mods:
  stmt_state_rel H ctx func cenv cx ee s /\
  MEM (tr,rootk,root) (FST H) /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\ storage_subregion root path delta tv /\
  w2n k = w2n rootk + delta /\ 0 < type_slot_size tv /\
  w2n k + type_slot_size tv <= dimword (:256) /\
  well_formed_type_value tv /\ value_has_type tv v /\
  encode_value tv v = SOME writes /\ val_in_memory tv v off s.vs_memory /\
  (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
  store_copy_normalize s t = FOLDL (\q i. (if tr then tstore else sstore)
        (k+n2w i) (mload (off+32*i) s) q) s ks /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  stmt_state_rel H ctx func cenv cx
    (set_storage cx ee tr (apply_writes k writes (get_storage cx ee tr))) t
Proof
  strip_tac >>
  irule place_store_normalized_stmt_state >> qexistsl_tac [`s`, `sa`] >> simp[] >>
  qpat_assum `store_copy_normalize s t = _` (fn th => pure_rewrite_tac [th]) >>
  pure_rewrite_tac[slot_copy_fold_bank] >>
  qabbrev_tac `newbank = apply_writes k writes (get_storage cx ee tr)` >>
  `storage_agree (storage_dead H tr newbank) newbank
     (FOLDL (\st i. update_storage (k+n2w i) (mload (32*i+off) s) st)
       (if tr then contract_transient s else contract_storage s) ks)`
   suffices_by (strip_tac >> drule_all place_store_storage_replace >> Cases_on `tr` >> simp[]) >>
  drule_then (qspec_then `tr` assume_tac) (Q.GEN `tr` slot_copy_initial_bank_agree) >>
  drule_all_then strip_assume_tac place_store_root_layout >>
  simp[Abbr `newbank`] >>
  qabbrev_tac `start = w2n k` >>
  `n2w start = k` by simp[Abbr `start`] >>
  `!i. k + n2w i = n2w (start+i)` by
    (gen_tac >> qpat_assum `n2w start = k` (fn th => pure_once_rewrite_tac[GSYM th]) >>
     simp[wordsTheory.word_add_n2w]) >>
  `start < dimword (:256)` by simp[Abbr `start`] >>
  qpat_assum `!i. k + n2w i = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `n2w start = k` (fn th => pure_once_rewrite_tac[GSYM th]) >>
  qpat_x_assum `start = w2n rootk + delta` (mk_asm "origin") >>
  ho_match_mp_tac place_store_encoded_copy_agree_sparse >> asm_rewrite_tac[] >>
  qexistsl_tac [`rootk`,`root`,`path`,`delta`,`tv`,`v`] >> asm_rewrite_tac[] >>
  conj_tac >- (asm "origin" ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_assum `n2w start = k` (fn th => pure_once_rewrite_tac[GSYM th]) >>
  `32*i + off = off + 32*i` by decide_tac >>
  pop_assum (fn th => pure_once_rewrite_tac[th]) >>
  irule place_store_memory_live_at >> asm_rewrite_tac[] >>
  qexistsl_tac [`tv`,`v`] >> asm_rewrite_tac[]
QED

Theorem slot_copy_write_wf_mods:
  regions_consistent (FST H) /\ storage_well_formed_on cx ee (FST H) /\
  storage_place_observed H (StoragePlace tr slot tv) /\
  well_formed_type_value tv /\ value_has_type tv v /\
  write_place cx (StoragePlace tr slot tv) v ee = (INL (),ef) ==>
  storage_well_formed_on cx ef (FST H)
Proof
  simp[storage_place_observed_def] >> strip_tac >>
  drule_all_then strip_assume_tac place_store_root_layout >>
  qpat_assum `write_place _ _ _ _ = _`
    (mp_then Any mp_tac write_place_preserves_storage_well_formed_on) >>
  rename1 `MEM (tr,root,rtv) (FST H)` >>
  disch_then (qspecl_then [`[StorageRoot tr (w2n root) rtv]`, `tv`, `H`] mp_tac) >>
  simp[storage_observations_ok_def, storage_trace_regions_def,
       storage_trace_locks_def, storage_roots_fit_def,
       storage_trace_backends_well_formed_def, wordsTheory.n2w_w2n,
       runtime_place_typed_def, place_type_value_def, return_def] >>
  metis_tac[]
QED
