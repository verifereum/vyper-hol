Theory exprSimAggregateBodyHeader
Ancestors
  exprSimProps exprLoweringProps localPtrsProps loweringSlice
  valueEncodingProps immutableMemoryFrame compileEnv venomState
  exprSimCopy

Theorem aggregate_body_header_state_rel[local]:
  stmt_state_rel ctx func ce cx es s /\
  (!name lo sz. local_region ce es.scopes s name lo sz ==>
     lo + sz <= b \/ b + 32 <= lo) /\
  (ce.ce_is_ctor ==> !name tv v io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint io (type_memory_size tv) b 32) ==>
  stmt_state_rel ctx func ce cx es (mstore b w s)
Proof
  strip_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
  rewrite_tac[Once stmt_state_rel_def] >> strip_tac >>
  `local_ptrs_rel func ce es.scopes (mstore b w s)` by
    (irule local_ptrs_rel_mstore >> gvs[state_rel_def] >> metis_tac[]) >>
  `immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es
     (mstore b w s)` by
    (irule immutables_rel_mem_agree >> qexists_tac `s` >>
     simp[immutable_mstore_capacity] >>
     conj_tac >- simp[mstore_def] >>
     reverse conj_tac >- gvs[state_rel_def] >>
     rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >>
     first_x_assum drule_all >> simp[regions_disjoint_def]) >>
  rewrite_tac[stmt_state_rel_def] >>
  conj_tac
  >- (irule state_rel_frame >> conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`es`, `s`] >> simp[] >> simp[mstore_def]) >>
  conj_tac
  >- (irule alloca_inv_fields >> qexists_tac `s` >> simp[mstore_def]) >>
  conj_tac
  >- (irule alloca_room_fields >> qexists_tac `s` >> simp[mstore_def]) >>
  conj_tac
  >- (irule fmp_room_fields >> qexists_tac `s` >> simp[mstore_def]) >>
  conj_tac
  >- (irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es`] >>
      simp[mstore_def] >> rpt strip_tac >> qexists_tac `id` >>
      fs[local_region_def, lookup_var_def]) >>
  conj_tac
  >- (irule immutable_base_zero_frame >> qexists_tac `s` >>
      simp[mstore_def, lookup_var_def]) >>
  simp[mstore_def] >> first_assum MATCH_ACCEPT_TAC
QED

Theorem aggregate_body_header_store_boundary:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [x] /\
  not_local_ptr ce es.scopes x /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,asz) /\ 32 <= asz /\
  (ce.ce_is_ctor ==> !name tv v io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint io (type_memory_size tv) b 32) ==>
  stmt_state_rel ctx func ce cx es (mstore b w s) /\
  locals_kept ce es s (mstore b w s) /\
  mem_word_at b (mstore b w s).vs_memory = w /\
  (!p n. p+n <= b \/ b+32 <= p ==>
    mem_bytes_at p n (mstore b w s).vs_memory = mem_bytes_at p n s.vs_memory)
Proof
  strip_tac >>
  `!name lo sz. local_region ce es.scopes s name lo sz ==>
     lo + sz <= b \/ b + 32 <= lo` by
    (rpt strip_tac >>
     fs[stmt_state_rel_def, state_rel_def] >>
     drule_all local_ptrs_rel_alloca_disjoint >>
     simp[regions_disjoint_def] >> decide_tac) >>
  conj_tac >- (irule aggregate_body_header_state_rel >> metis_tac[]) >>
  conj_tac
  >- (irule locals_kept_regions >> rpt strip_tac >>
      irule mstore_mem_bytes_at_disjoint >> metis_tac[]) >>
  simp[mstore_mem_word_at_same] >> rpt strip_tac >>
  irule mstore_mem_bytes_at_disjoint >> decide_tac
QED
