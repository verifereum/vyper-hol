(* Storage and transient taint at a fixed payload-then-header endpoint. *)
Theory bodyAppendSlotTaintMods
Ancestors
  bodyFullAppendNestedFrames bodyFullAppendLocalFrames bodyFullShadowBodyInv
  stmtSimAssignStorageCopy stateRelProj exprLoweringProps loweringStateRelDefs
  bodyPtrDefs sourceUnitExecution accountsRelProps placeStoreStorage
  vyperStoragePlaceObserved vyperStoragePlaceRegion vyperStorageFootprint
  vyperStorageBackend vyperEncodeDecode vyperStorage vyperValue vyperTyping
  venomState vfmState ptrDiscipline pred_set words list

Theorem append_slot_taint_layout[local]:
  storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) /\
  regions_consistent (FST H) ==>
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
  qexistsl_tac [`root`,`tv'`,`path`,`delta`] >> simp[word_add_def,w2n_n2w]
QED

Theorem append_slot_bank_mask[local]:
  stmt_state_rel H ctx func cenv cx es s /\ dead_lo_ok_mods H D lo cenv cx ==>
  !tr. (if tr then D.d_trans s.vs_call_ctx.cc_address (contract_transient s)
        else D.d_stor s.vs_call_ctx.cc_address (contract_storage s)) =
       {(q,b) | storage_dead H tr (get_storage cx es tr) (w2n q) b}
Proof
  strip_tac >> gen_tac >>
  `s.vs_call_ctx.cc_address = cx.txn.target` by
    (drule_then assume_tac stmt_state_rel_state_rel >> drule state_rel_call_ctx_rel >>
     simp[call_ctx_rel_def]) >>
  drule_all_then (qspec_then `tr` assume_tac) storage_copy_initial_agree >>
  drule_then assume_tac storage_agree_storage_dead >>
  Cases_on `tr` >> gvs[dead_lo_ok_mods_def,cx_dead_def]
QED

Theorem append_slot_taint_sparse_bound[local]:
  MEM (tr,rootk,root) (FST H) /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_subregion root path delta (ArrayTV tv (Dynamic cap)) /\
  w2n slot = w2n rootk + delta /\ w2n rootk + type_slot_size root <= dimword (:256) /\
  well_formed_type_value tv /\ value_has_type tv v /\ len < cap /\
  k = slot+n2w (1+len*type_slot_size tv) /\ encode_value tv v = SOME writes /\
  (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
  (!m. mem_agree_outside M mem m ==> val_in_memory tv v off m) /\
  X SUBSET {(q,b) | storage_dead H tr st (w2n q) b} ==>
  key_update
    (FOLDL (\Y j. key_update Y (k+n2w j) (mem_word_taint M (off+32*j))) X ks)
    slot {} SUBSET
  {(q,b) | storage_dead H tr (update_storage slot h (apply_writes k writes st)) (w2n q) b}
Proof
  strip_tac >> Cases_on `type_slot_size tv = 0`
  >- (`!i. ~MEM i (MAP FST writes)` by
        metis_tac[cj 1 encode_writes_bounded,prim_recTheory.NOT_LESS_0] >>
      `writes = [] /\ ks = []` by
        (conj_tac >- (Cases_on `writes` >> fs[] >> metis_tac[]) >>
         Cases_on `ks` >> fs[] >> metis_tac[]) >>
      `!j b. storage_dead H tr (update_storage slot h st) j b <=>
             storage_dead H tr st j b` by
        (rpt gen_tac >> irule append_subregion_header_storage_dead >> asm_rewrite_tac[] >>
         qexistsl_tac [`cap`,`delta`,`path`,`root`,`rootk`,`tv`] >> asm_rewrite_tac[]) >>
      gvs[apply_writes_def] >>
      irule SUBSET_TRANS >> qexists `X` >> simp[] >>
      simp[SUBSET_DEF,key_update_def,pairTheory.FORALL_PROD]) >>
  `0 < type_slot_size tv` by decide_tac >>
  `w2n k + type_slot_size tv <= dimword (:256)` by
    drule_all_then (ACCEPT_TAC o cj 3) append_observed_child >>
  `!j b. j < type_slot_size tv /\ b < 32 /\ MEM j (MAP FST writes) /\
         ~dead_bytes (apply_writes k writes st) (w2n k) tv (w2n k+j) b ==>
         off+32*j+b NOTIN M` by
    (rpt gen_tac >> strip_tac >> drule_all_then ACCEPT_TAC append_encoded_live_byte_clean) >>
  irule append_subregion_sparse_keys_dead >> asm_rewrite_tac[] >>
  qexistsl_tac [`cap`,`delta`,`len`,`path`,`root`,`rootk`,`tv`,`v`] >> gvs[]
QED

Theorem append_slot_taint_mods:
  stmt_state_rel H ctx func cenv cx es s /\ stmt_state_rel H ctx func cenv cx ef u /\
  ghost_inv_at_mods (DF H) lo d cenv cx es G tn s /\ dead_lo_ok_mods H (DF H) lo cenv cx /\
  storage_place_observed H (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) /\
  regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
  len < cap /\ k = slot+n2w (1+len*type_slot_size tv) /\
  well_formed_type_value tv /\ value_has_type tv v /\ encode_value tv v = SOME writes /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v off mem) /\
  (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
  ef = set_storage cx es tr
    (update_storage slot (n2w (len+1)) (apply_writes k writes (get_storage cx es tr))) /\
  u.vs_immutables = s.vs_immutables /\ tf.t_imm = tn.t_imm /\
  (if tr then tf.t_stor = tn.t_stor else tf.t_trans = tn.t_trans) /\
  (if tr then tf.t_trans else tf.t_stor) SUBSET
    key_update
      (FOLDL (\Y j. key_update Y (k+n2w j) (mem_word_taint tn.t_mem (off+32*j)))
        (if tr then tn.t_trans else tn.t_stor) ks) slot {} ==>
  stor_taint_ok_at (DF H) tf u
Proof
  strip_tac >>
  `stor_taint_ok_at (DF H) tn s` by fs[ghost_inv_at_mods_def] >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` kall_tac >>
  drule_all_then strip_assume_tac append_slot_taint_layout >>
  `get_storage cx ef (~tr) = get_storage cx es (~tr)` by
    (qpat_assum `ef = set_storage _ _ _ _` SUBST1_TAC >>
     irule get_storage_after_set_other >> Cases_on `tr` >> simp[]) >>
  `get_storage cx ef tr =
    update_storage slot (n2w (len+1)) (apply_writes k writes (get_storage cx es tr))` by
    simp[get_storage_after_set] >>
  qpat_assum `stmt_state_rel _ _ _ _ _ es s`
    (mp_then (Pos hd) (drule_then assume_tac) append_slot_bank_mask) >>
  qpat_assum `stmt_state_rel _ _ _ _ _ ef u`
    (mp_then (Pos hd) (drule_then assume_tac) append_slot_bank_mask) >>
  `(if tr then tn.t_trans else tn.t_stor) SUBSET
    {(q,b) | storage_dead H tr (get_storage cx es tr) (w2n q) b}` by
    (qpat_assum `!b. (if b then _ _ (contract_transient s) else _) = _`
       (qspec_then `tr` (fn th => rewrite_tac[GSYM th])) >>
     Cases_on `tr` >> fs[stor_taint_ok_at_def,contract_storage_def,
                         contract_transient_def,lookup_account_def]) >>
  `(if tr then tf.t_trans else tf.t_stor) SUBSET
    {(q,b) | storage_dead H tr (get_storage cx ef tr) (w2n q) b}` by
    (irule SUBSET_TRANS >> goal_assum (drule_at Any) >>
     qpat_assum `get_storage cx ef tr = _` SUBST1_TAC >>
     irule append_slot_taint_sparse_bound >> asm_rewrite_tac[] >>
     qexistsl_tac [`cap`,`delta`,`len`,`s.vs_memory`,`path`,`root`,`rootk`,`tv`,`v`] >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `ef = set_storage _ _ _ _` kall_tac >>
  rpt (qpat_x_assum `!b. (if b then _ else _) = _`
    (fn th => map_every (fn b => qspec_then b assume_tac th) [`T`,`F`])) >>
  Cases_on `tr` >>
  gvs[stor_taint_ok_at_def,contract_transient_def,contract_storage_def,lookup_account_def]
QED
