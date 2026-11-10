(* Sparse storage semantics with explicit declared-root layout facts. *)
Theory storeSlotsStorageRegion
Ancestors
  placeStoreSlots placeStoreStorage stmtSimAssignStorageCopy
  exprSimDefs stmtSimDefs exprLoweringProps compileEnv venomState vyperStorage vyperTyping words list

Theorem store_slots_fold_state_layout[local]:
  stmt_state_rel ctx func cenv cx ee s /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta tv /\ start = w2n rootk + delta /\
  w2n rootk + type_slot_size root <= dimword (:256) /\
  (!mid' name' subs' k' tv'.
    declared_storage_region cx mid' name' subs' = SOME (tr,k',tv') /\
    (k',tv') <> (rootk,root) ==>
    ranges_disjoint (w2n rootk) (type_slot_size root) (w2n k') (type_slot_size tv')) /\
  0 < type_slot_size tv /\ encode_value tv v = SOME writes /\ value_has_type tv v /\
  start + type_slot_size tv <= dimword (:256) /\
  (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
  (!i b. i < type_slot_size tv /\ b < 32 /\ MEM i (MAP FST writes) /\
    ~dead_bytes (apply_writes (n2w start) writes (get_storage cx ee tr))
       start tv (start+i) b ==>
    EL b (word_to_bytes (lookup_storage (n2w (start+i))
      (apply_writes (n2w start) writes (get_storage cx ee tr))) T) =
    EL b (word_to_bytes (rd i) T)) ==>
  stmt_state_rel ctx func cenv cx
    (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr)))
    (FOLDL (\t i. (if tr then tstore else sstore)
       (n2w (start+i)) (rd i) t) s ks)
Proof
  strip_tac >>
  `storage_agree (storage_dead cx tr (get_storage cx ee tr))
    (get_storage cx ee tr)
    (if tr then contract_transient s else contract_storage s)` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     Cases_on `tr` >>
     simp[stmt_state_rel_def, state_rel_def, accounts_rel_def,
          accounts_agree_def, transient_agree_def,
          vyperStorageBackendTheory.get_storage_def,
          vfmStateTheory.lookup_account_def,
          contract_storage_def, contract_transient_def,
          call_ctx_rel_def] >> metis_tac[]) >>
  `storage_agree
    (storage_dead cx tr (apply_writes (n2w start) writes (get_storage cx ee tr)))
    (apply_writes (n2w start) writes (get_storage cx ee tr))
    (FOLDL (\st i. update_storage (n2w (start+i)) (rd i) st)
      (if tr then contract_transient s else contract_storage s) ks)` by
    (irule place_store_encoded_copy_agree_sparse >> metis_tac[]) >>
  pure_rewrite_tac [GSYM wordsTheory.word_add_n2w, storage_copy_backend_fold] >>
  drule_all place_store_storage_replace >> Cases_on `tr` >>
  simp[wordsTheory.word_add_n2w]
QED

Theorem store_slots_semantic_endpoint_layout:
  evaluate_type (get_tenv cx) dty = SOME tv /\
  stmt_state_rel ctx fn cenv cx ee s /\ local_ptrs_reserved cenv sa /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta tv /\ start = w2n rootk + delta /\
  w2n rootk + type_slot_size root <= dimword (:256) /\
  (!mid' name' subs' k' tv'.
    declared_storage_region cx mid' name' subs' = SOME (tr,k',tv') /\
    (k',tv') <> (rootk,root) ==>
    ranges_disjoint (w2n rootk) (type_slot_size root) (w2n k') (type_slot_size tv')) /\
  0 < type_slot_size tv /\ encode_value tv v = SOME writes /\ value_has_type tv v /\
  start + type_slot_size tv <= dimword (:256) /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  store_copy_normalize s t =
    FOLDL (\q j. (if tr then tstore else sstore)
      (n2w start + n2w j) (mload (w2n sw + 32*j) s) q) s ks /\
  (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  stmt_state_rel ctx fn cenv cx
    (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr))) t
Proof
  strip_tac >>
  `start < dimword (:256)` by decide_tac >>
  `well_formed_type_value tv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  irule place_store_normalized_stmt_state >>
  goal_assum (drule_at (Pat `local_ptrs_reserved _ _`)) >>
  qexists_tac `s` >> asm_simp_tac bool_ss [] >>
  qpat_x_assum `store_copy_normalize _ _ = _` SUBST1_TAC >>
  pure_rewrite_tac [wordsTheory.word_add_n2w] >>
  ho_match_mp_tac store_slots_fold_state_layout >>
  goal_assum (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  asm_simp_tac bool_ss [] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> irule place_store_memory_live_at >> metis_tac[]
QED
