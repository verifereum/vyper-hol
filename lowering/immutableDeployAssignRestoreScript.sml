(* Final-store restoration starts after any allocating normalization. *)
Theory immutableDeployAssignRestore
Ancestors
  immutableDeployAssignStateFrame immutableDeployAssignMemoryFrame
  immutableDeployAssignSourceFrame immutableDeployAssignFacts
  exprLoweringProps exprSimHypsDefs compileEnv loweringStateRelDefs vyperPlaceFrames vyperState
  venomState finite_map

Theorem immutable_store_stmt_state_rel:
  stmt_state_rel ctx func ce cx es s /\ expr_sim_inv ce cx env es /\
  local_ptrs_reserved ce sa /\ ce.ce_is_ctor /\ src = ce.ce_module /\
  FLOOKUP env.bare_globals (src,id) = SOME ty /\
  FLOOKUP ce.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  write_place cx (ImmutablePlace src id []) v es = (INL (),es') /\
  immutable_value_admissible tv v /\ val_in_memory tv v off q.vs_memory /\
  immutable_value_bytes_rel tv v
    (mem_bytes_at off (type_memory_size tv) q.vs_memory) /\
  (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_immutables := s.vs_immutables; vs_prev_bb := s.vs_prev_bb;
    vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
  LENGTH s.vs_memory <= LENGTH q.vs_memory /\
  (!a k. regions_disjoint a k off (type_memory_size tv) ==>
    mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) ==>
  stmt_state_rel ctx func ce cx es' q
Proof
  strip_tac >> gvs[] >>
  `q.vs_allocas = s.vs_allocas /\ q.vs_alloca_next = s.vs_alloca_next /\
   q.vs_fmp = s.vs_fmp /\ q.vs_labels = s.vs_labels /\
   q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
   q.vs_call_ctx = s.vs_call_ctx /\ q.vs_tx_ctx = s.vs_tx_ctx /\
   q.vs_block_ctx = s.vs_block_ctx /\ q.vs_logs = s.vs_logs /\
   q.vs_outcomes = s.vs_outcomes /\ q.vs_requests = s.vs_requests /\
   q.vs_pending_deletions = s.vs_pending_deletions` by
    (qpat_x_assum `_ = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `?imms. es' = es with immutables := imms` by
    (drule write_immutable_place_frame >> simp[]) >>
  `?mods old. ALOOKUP es.immutables cx.txn.target = SOME mods /\
    FLOOKUP (get_source_immutables ce.ce_module mods) id = SOME (tv,old)` by
    (drule_all immutable_assign_source_lookup >> simp[]) >>
  `ce.ce_module_var_type (ce.ce_module,id) = SOME ty` by
    (drule_all immutable_assign_target_layout >> simp[]) >>
  `local_ptrs_rel func ce es.scopes s /\
   immutable_decl_sep ce cx es.scopes s.vs_vars s.vs_allocas s.vs_alloca_next /\
   immutable_alloca_sep func ce cx es s /\ immutable_base_zero ce s /\
   immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es s` by
    (fs[stmt_state_rel_def, state_rel_def, immutable_alloca_sep_def] >>
     first_assum ACCEPT_TAC) >>
  `local_ptrs_rel func ce es'.scopes q` by
    (gvs[] >> irule immutable_store_local_ptrs_frame >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `immutable_alloca_sep func ce cx es' q` by
    (drule_all immutable_store_alloca_sep_frame >> simp[]) >>
  `immutable_base_zero ce q` by
    (irule immutable_base_zero_frame >> qexists_tac `s` >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es' q` by
    (drule_all immutable_store_immutables_frame >> simp[]) >>
  irule stmt_state_rel_allocas_frame >> simp[] >>
  reverse conj_tac >- (qexistsl_tac [`es`, `s`] >> simp[]) >>
  gvs[state_rel_def, stmt_state_rel_def, storage_rel_def, transient_rel_def,
      accounts_rel_def, logs_rel_def, contract_storage_def, contract_transient_def]
QED
