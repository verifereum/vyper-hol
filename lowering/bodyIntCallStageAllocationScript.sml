(* A single counted fresh allocation, preserving all held observations. *)
Theory bodyIntCallStageAllocation
Ancestors
  bodyIntCallStorageAllocate bodyIntCallHeldByteFrame
  exprSimAggregateChildren loweringHalt venomMemDefs venomState finite_map
  loweringPosts exprLoweringProps compileEnv context actualAllocExec venomInst

Theorem intcall_stage_allocation:
  compile_alloc_buffer nb sm = (buf,si) /\ fn_has_code sm si func /\
  nb < dimword (:256) /\ sm.cs_next_id NOTIN FDOM s.vs_allocas /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ intcall_held_args ce cx a sm es s H /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u x inst.
    buf.buf_operand = Var x /\ MEM inst (fn_insts func) /\
    inst.inst_id = sm.cs_next_id /\ inst.inst_outputs = [x] /\
    inst.inst_opcode = ALLOCA /\
    inst.inst_id < si.cs_next_id /\ not_fresh_at si x /\
    local_ptrs_reserved ce si /\ (!scopes. not_local_ptr ce scopes x) /\
    gas_marked_path F ctx func s 0 (OK u) /\
    u = (update_var x (n2w s.vs_alloca_next)
      (s with <|vs_allocas := s.vs_allocas |+
        (sm.cs_next_id,(s.vs_alloca_next,nb));
        vs_alloca_next := s.vs_alloca_next + nb|>)) with
      vs_inst_idx := LENGTH si.cs_current_insts /\
    ~u.vs_halted /\ u.vs_current_bb = si.cs_current_bb /\
    u.vs_inst_idx = LENGTH si.cs_current_insts /\
    eval_operand buf.buf_operand u = SOME (n2w s.vs_alloca_next) /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (s.vs_alloca_next,nb) /\
    u.vs_alloca_next = s.vs_alloca_next + nb /\
    stmt_state_rel ctx func ce cx es u /\
    intcall_held_args ce cx a si es u H /\ wb_frame ce es sm s u /\
    u.vs_memory = s.vs_memory /\
    (!y. not_fresh_at sm y ==> lookup_var y u = lookup_var y s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid lb sz. FLOOKUP s.vs_allocas aid = SOME (lb,sz) ==>
       compileEnv$regions_disjoint s.vs_alloca_next nb lb sz)
Proof
  strip_tac >> drule_all fresh_buffer_allocation_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all buffer_alloc_provenance >> strip_tac >>
  `stmt_state_rel ctx func ce cx es u` by
    (irule (cj 1 fresh_buffer_allocation_state_rel) >>
     metis_tac[arithmeticTheory.ADD_COMM]) >>
  `!y. not_fresh_at sm y ==> lookup_var y u = lookup_var y s` by
    (rpt strip_tac >> simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `wb_frame ce es sm s u /\ intcall_held_args ce cx a si es u H` by
    suspend "held" >>
  `!aid lb sz. FLOOKUP s.vs_allocas aid = SOME (lb,sz) ==>
     compileEnv$regions_disjoint s.vs_alloca_next nb lb sz` by
    (gvs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def,
         compileEnvTheory.regions_disjoint_def] >> metis_tac[]) >>
  drule_all actual_alloc_buffer_site >> disch_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  qexistsl_tac [`u`, `x`,
    `mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)]
       [STRING #"%" (toString sm.cs_next_var)]`] >>
  simp[mk_inst_def] >>
  qpat_x_assum `u = _` SUBST_ALL_TAC >>
  simp[update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[FLOOKUP_DEF] >> metis_tac[]
QED

Resume intcall_stage_allocation[held]:
  drule compile_alloc_buffer_parts >> strip_tac >>
  irule intcall_held_allocation_bytes_frame >>
  simp[update_var_def, contract_storage_def, contract_transient_def] >>
  reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [`sm.cs_next_id`, `nb`, `si`, `u`] >>
  simp[update_var_def]
QED
Finalise intcall_stage_allocation
