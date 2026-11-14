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

Theorem intcall_append_aggregate_copy:
  compile_store_slots ce src dst dty tr sa = ((),sb) /\
  evaluate_type (get_tenv cx) dty = SOME tv /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME (n2w start) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  local_ptrs_reserved ce sa /\
  expr_sim_inv ce cx env ee /\ stmt_state_rel ctx func ce cx ee s /\
  declared_storage_region cx mid name subs = SOME (tr,rootk,root) /\
  storage_subregion root path delta tv /\ start = w2n rootk + delta /\
  0 < type_slot_size tv /\ encode_value tv v = SOME writes /\ value_has_type tv v /\
  start + type_slot_size tv <= dimword (:256) /\
  val_in_memory tv v (w2n sw) s.vs_memory ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx
      (set_storage cx ee tr (apply_writes (n2w start) writes (get_storage cx ee tr))) t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `start < dimword (:256)` by decide_tac >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(fname,fty,sz). !tv.
        evaluate_type (get_tenv cx) fty = SOME tv ==>
        sz = type_memory_size tv) fields)` by
    (fs[exprSimHypsDefsTheory.expr_sim_inv_def] >> metis_tac[]) >>
  `store_slots_entry ce ctx dty tv v` by
    (irule store_slots_rank_entry >> simp[] >> qexists `get_tenv cx` >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `store_slots_entry _ _ _ _ _` mp_tac >>
  rewrite_tac[store_slots_entry_def] >>
  disch_then (drule_at (Pat `compile_store_slots _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`func`,`s`,`sw`,`n2w start`] mp_tac) >>
  disch_then (qspec_then `writes` mp_tac) >>
  (impl_tac >- (simp[wordsTheory.w2n_n2w] >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`t`,`ks`] strip_assume_tac) >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (drule intcall_store_slots_normalize_frontier >> simp[]) >>
  drule_all intcall_store_slots_sparse_landing >>
  strip_tac >> qexists `t` >> simp[]
QED
