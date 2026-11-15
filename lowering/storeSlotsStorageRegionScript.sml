(* Sparse storage semantics over the observed finite storage roots. *)
Theory storeSlotsStorageRegion
Ancestors
  loweringStateRelDefs
  placeStoreSlots placeStoreStorage stmtSimAssignStorageCopy
  exprSimDefs stmtSimDefs exprLoweringProps compileEnv venomState vyperStorage vyperTyping words list

Theorem store_slots_semantic_endpoint_layout:
  evaluate_type (get_tenv cx) dty = SOME tv /\
  expr_sim_inv cenv cx env ee /\
  stmt_state_rel H ctx fn cenv cx ee s /\ local_ptrs_reserved cenv sa /\
  MEM (tr,rootk,root) (FST H) /\ regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_subregion root path delta tv /\ start = w2n rootk + delta /\
  w2n rootk + type_slot_size root <= dimword (:256) /\
  0 < type_slot_size tv /\ encode_value tv v = SOME writes /\ value_has_type tv v /\
  start + type_slot_size tv <= dimword (:256) /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  store_copy_normalize s t =
    FOLDL (\q j. (if tr then tstore else sstore)
      (n2w start + n2w j) (mload (w2n sw + 32*j) s) q) s ks /\
  (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  stmt_state_rel H ctx fn cenv cx
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
  irule (Q.INST [`env` |-> `env`, `rootk` |-> `rootk`,
    `root` |-> `root`, `path` |-> `path`, `delta` |-> `delta`, `v` |-> `v`]
    place_store_encoded_leaf_state_sparse) >>
  simp[] >>
  rpt strip_tac >> irule place_store_memory_live_at >> metis_tac[]
QED
