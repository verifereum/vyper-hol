Theory nonreentrantSource
Ancestors
  words finite_map
  compileEnv loweringStateRelDefs accountsRelProps
  vyperInterpreter vyperState vyperContext vyperStorageLayoutSafety
  venomState vfmState vfmExecution

(* Layout safety reserves the whole lock word outside every declared
   transient region, including bytes ignored by the storage relation. *)
Theorem nonreentrant_storage_live:
  storage_layout_safe cx /\ cx.nonreentrant_slot = SOME nkey ==>
  ~storage_dead cx T st (w2n ((n2w nkey):bytes32)) b
Proof
  strip_tac >>
  drule_all storage_layout_safe_nonreentrant_slot_nonoverflow >> strip_tac >>
  simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  pure_rewrite_tac[storage_dead_def] >> strip_tac >>
  drule_all storage_layout_safe_nonreentrant_slot_separation >>
  drule (cj 1 dead_bytes_range) >>
  simp[vyperStorageFrameTheory.ranges_disjoint_def] >> decide_tac
QED

Theorem nonreentrant_region_frame[local]:
  storage_layout_safe cx /\ cx.nonreentrant_slot = SOME nkey /\
  declared_storage_region cx mid n subs = SOME (T,slot,tv) /\
  w2n slot + type_slot_size tv <= dimword (:256) ==>
  (dead_bytes (update_storage (n2w nkey) v st) (w2n slot) tv j b <=>
   dead_bytes st (w2n slot) tv j b)
Proof
  strip_tac >> irule (cj 1 dead_bytes_frame) >> rpt strip_tac >>
  drule_all storage_layout_safe_nonreentrant_slot_separation >>
  drule_all storage_layout_safe_nonreentrant_slot_nonoverflow >>
  rpt strip_tac >>
  `i < dimword (:256) /\ nkey < dimword (:256) /\ i <> nkey` by
    (gvs[vyperStorageFrameTheory.ranges_disjoint_def] >> decide_tac) >>
  `((n2w i):bytes32) <> n2w nkey` by
    (simp[wordsTheory.n2w_11, arithmeticTheory.LESS_MOD]) >>
  simp[lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem nonreentrant_storage_dead_frame:
  storage_layout_safe cx /\ cx.nonreentrant_slot = SOME nkey ==>
  (storage_dead cx T (update_storage (n2w nkey) v st) j b <=>
   storage_dead cx T st j b)
Proof
  strip_tac >> pure_rewrite_tac[storage_dead_def] >>
  eq_tac >> strip_tac >>
  drule_all nonreentrant_region_frame >> strip_tac >>
  metis_tac[]
QED

Theorem nonreentrant_lock_agreement:
  state_rel func cenv cx es ss /\ storage_layout_safe cx /\
  cx.nonreentrant_slot = SOME nkey ==>
  lookup_storage (n2w nkey) (es.tStorage cx.txn.target) =
    tload (n2w nkey) ss
Proof
  strip_tac >>
  `!b. ~storage_dead cx T (es.tStorage cx.txn.target)
           (w2n ((n2w nkey):bytes32)) b` by
    (gen_tac >> irule nonreentrant_storage_live >> metis_tac[]) >>
  gvs[state_rel_def, transient_rel_def, tload_def,
      contract_transient_def] >>
  irule word_to_bytes_EL_eq >> rpt strip_tac >>
  gvs[storage_agree_def] >> metis_tac[]
QED

Theorem nonreentrant_state_rel_write:
  state_rel func cenv cx es ss /\ storage_layout_safe cx /\
  cx.nonreentrant_slot = SOME nkey ==>
  state_rel func cenv cx
    (es with tStorage := (cx.txn.target =+
      update_storage (n2w nkey) v (es.tStorage cx.txn.target)) es.tStorage)
    (tstore (n2w nkey) v ss)
Proof
  strip_tac >>
  `accounts_rel cx es ss /\ ss.vs_call_ctx.cc_address = cx.txn.target` by
    gvs[state_rel_def, call_ctx_rel_def] >>
  `transient_agree cx
    ((cx.txn.target =+ update_storage (n2w nkey) v
       (es.tStorage cx.txn.target)) es.tStorage)
    ((cx.txn.target =+ update_storage (n2w nkey) v
       (ss.vs_transient cx.txn.target)) ss.vs_transient)` by
    (irule transient_agree_update >> reverse conj_tac
     >- gvs[accounts_rel_def] >>
     rpt strip_tac >>
     drule_all nonreentrant_storage_dead_frame >> simp[]) >>
  qmatch_goalsub_abbrev_tac `state_rel func cenv cx es1 ss1` >>
  `accounts_rel cx es1 ss1` by
    gvs[Abbr `es1`, Abbr `ss1`, accounts_rel_def, tstore_def] >>
  `storage_rel cx cx.txn.target es1 ss1 /\
   transient_rel cx cx.txn.target es1 ss1` by
    (drule accounts_rel_storage_transient >>
     gvs[Abbr `ss1`, tstore_def]) >>
  gvs[state_rel_def, Abbr `es1`, Abbr `ss1`, tstore_def,
      local_ptrs_rel_def, local_backed_def, local_region_def, lookup_var_def,
      immutables_rel_def, logs_rel_def] >>
  asm_rewrite_tac[]
QED

Theorem source_nonreentrant_lock_state_rel:
  !func cenv cx es ss nkey is_view.
    state_rel func cenv cx es ss /\ storage_layout_safe cx /\
    cx.nonreentrant_slot = SOME nkey ==>
    lookup_storage (n2w nkey) (es.tStorage cx.txn.target) =
      tload (n2w nkey) ss /\
    (!es'. acquire_nonreentrant_lock cx.txn.target nkey is_view es =
             (INL (), es') ==>
           state_rel func cenv cx es'
             (if is_view then ss else tstore (n2w nkey) 1w ss))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule nonreentrant_lock_agreement >> metis_tac[]) >>
  gen_tac >>
  simp[acquire_nonreentrant_lock_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def,
       get_transient_storage_def, update_transient_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
       vfmExecutionTheory.lookup_transient_storage_def,
       vfmExecutionTheory.update_transient_storage_def] >>
  Cases_on `lookup_storage (n2w nkey) (es.tStorage cx.txn.target) = 1w`
  >- simp[vyperStateTheory.raise_def] >>
  Cases_on `is_view`
  >- (simp[vyperStateTheory.return_def] >> metis_tac[]) >>
  simp[update_transient_def, vyperStateTheory.return_def] >>
  strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `state_rel func cenv cx es1 _` >>
  `es1 = es with tStorage := (cx.txn.target =+
      update_storage (n2w nkey) 1w (es.tStorage cx.txn.target)) es.tStorage` by
    simp[Abbr `es1`, evaluation_state_component_equality,
         vfmExecutionTheory.update_transient_storage_def] >>
  gvs[] >> irule nonreentrant_state_rel_write >> metis_tac[]
QED
