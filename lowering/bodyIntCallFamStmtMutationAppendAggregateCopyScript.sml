(* Sparse storage updates retain the allocation frontier. *)
Theory bodyIntCallFamStmtMutationAppendAggregateCopy
Ancestors
  placeStoreSlots stmtSimStoreCopy venomState list words

Theorem intcall_store_slots_normalize_frontier:
  store_copy_normalize s t =
    FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
             (mload (w2n sw + 32*j) s) q) s ks ==>
  t.vs_alloca_next = s.vs_alloca_next
Proof
  `!ks a. (FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
                 (mload (w2n sw + 32*j) s) q) a ks).vs_alloca_next =
           a.vs_alloca_next` by
    (Induct >> simp[FOLDL] >> gen_tac >> Cases_on `tr` >>
     gvs[sstore_def,tstore_def]) >>
  disch_then (mp_tac o AP_TERM ``\u:venom_state. u.vs_alloca_next``) >>
  simp[store_copy_normalize_def]
QED

Theorem intcall_store_slots_sparse_landing:
  expr_sim_inv ce cx env ee /\ stmt_state_rel ctx func ce cx ee s /\
  local_ptrs_reserved ce sa /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta tv /\ start = w2n rootk + delta /\
  0 < type_slot_size tv /\ encode_value tv v = SOME writes /\
  value_has_type tv v /\ start + type_slot_size tv <= dimword (:256) /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  store_copy_normalize s t =
    FOLDL (\q j. (if tr then tstore else sstore) (n2w start + n2w j)
             (mload (w2n sw + 32*j) s) q) s ks /\
  (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  t.vs_allocas = s.vs_allocas ==>
  stmt_state_rel ctx func ce cx
    (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr))) t
Proof
  strip_tac >>
  `well_formed_type_value tv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  `start < dimword (:256)` by decide_tac >>
  irule placeStoreStorageTheory.place_store_normalized_stmt_state >>
  goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
  qexists `s` >> pure_asm_rewrite_tac[] >>
  conj_tac >- simp[] >>
  qpat_x_assum `store_copy_normalize _ _ = _` SUBST1_TAC >>
  pure_rewrite_tac[wordsTheory.word_add_n2w] >>
  ho_match_mp_tac place_store_encoded_leaf_state_sparse >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  qexistsl [`env`,`path`,`delta`,`tv`,`v`] >>
  asm_simp_tac bool_ss [] >>
  conj_tac >- gvs[] >>
  rpt strip_tac >>
  irule placeStoreStorageTheory.place_store_memory_live_at >>
  simp[] >> qexistsl [`tv`,`v`] >> gvs[]
QED
