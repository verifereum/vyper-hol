Theory tupleAssignImmutableDeployIntRestore
Ancestors
  bodyIntCallSeams bodyMemoryDefs intCallReturn intCallFrame
  exprLoweringProps localPtrsProps loweringStateRelDefs
  accountsRelProps venomExecSemantics venomState
  exprSimDefs venomExecProofs list lowerDloadPtrReturn

Theorem tuple_immutable_intcall_return_restore_actual:
  !ctx func ce cx before t rtv rc rb n v ee ir cs' callee argv setup
   fuel outs u.
  stmt_state_rel ctx func ce cx before t /\
  intcall_callee_exit func ce cx rtv rc rb n t (INL v) ee (IntRet ir cs') /\
  setup_callee callee argv t = SOME setup /\
  run_blocks fuel ctx callee setup = IntRet ir cs' /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs')) = SOME u /\
  EVERY (not_local_ptr ce before.scopes) outs /\
  immutable_alloca_sep func ce cx (ee with scopes := before.scopes) t /\
  (!name b sz aid off asz.
    local_region ce before.scopes t name b sz /\
    FLOOKUP t.vs_allocas aid = SOME (off,asz) /\ n <= aid ==>
    regions_disjoint b sz off asz) ==>
  stmt_state_rel ctx func ce cx (ee with scopes := before.scopes) u
Proof
  rpt gen_tac >> strip_tac >>
  `state_rel func ce cx (ee with scopes := []) cs' /\
   ir.iret_adopt_fmp = NONE /\
   (!b sz. b + sz <= t.vs_alloca_next /\
     (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
       n <= aid ==> regions_disjoint b sz off asz) ==>
     mem_bytes_at b sz cs'.vs_memory = mem_bytes_at b sz t.vs_memory)` by
    (gvs[intcall_callee_exit_def, expr_exit_def] >> metis_tac[]) >>
  `local_ptrs_rel func ce before.scopes t` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `!name b sz. local_region ce before.scopes t name b sz ==>
     mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz cs'.vs_memory` by
    (rpt strip_tac >>
     `b + sz <= t.vs_alloca_next` by metis_tac[body_local_region_frontier] >>
     first_x_assum (qspecl_then [`b`, `sz`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `local_ptrs_rel func ce before.scopes u` by
    (irule invoke_return_local_ptrs_rel >> metis_tac[]) >>
  drule invoke_return_frame >> strip_tac >>
  `u.vs_labels = t.vs_labels /\ u.vs_fmp = t.vs_fmp` by
    (drule dload_bind_outputs_frame >>
     simp[adopt_return_fmp_def, merge_callee_state_def] >>
     disch_then SUBST1_TAC >> simp[]) >>
  `immutable_base_zero ce u` by
    (`immutable_base_zero ce t` by fs[stmt_state_rel_def] >>
     irule immutable_base_zero_frame >> qexists `t` >>
     gvs[EVERY_MEM, not_local_ptr_def] >> metis_tac[]) >>
  `setup.vs_data_section = t.vs_data_section` by gvs[setup_callee_def] >>
  drule run_blocks_intret_data_section >> strip_tac >>
  gvs[adopt_return_fmp_def, merge_callee_state_def, lookup_var_def] >>
  irule stmt_state_rel_allocas_frame >> simp[] >>
  conj_tac
  >- (irule immutable_alloca_sep_fields >>
      qexistsl [`t`, `ee with scopes := before.scopes`] >> simp[] >>
      rpt strip_tac >> qexists `id` >> gvs[local_region_def] >>
      gvs[EVERY_MEM, not_local_ptr_def, lookup_var_def] >> metis_tac[]) >>
  reverse conj_tac >- (qexistsl [`before`, `t`] >> simp[]) >>
  drule dload_bind_outputs_frame >> disch_then SUBST_ALL_TAC >>
  qpat_x_assum `stmt_state_rel ctx _ _ _ _ _` mp_tac >>
  qpat_x_assum `state_rel _ _ _ _ cs'` mp_tac >>
  simp[stmt_state_rel_def, state_rel_def, storage_rel_def, transient_rel_def,
       accounts_rel_def, logs_rel_def, call_ctx_rel_def,
       contract_storage_def, contract_transient_def, log_entry_equiv_def,
       immutables_rel_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!name tv v byte_offset. _` drule >>
  simp[] >> metis_tac[]
QED

Theorem tuple_immutable_intcall_return_restore_next:
  !ctx func ce cx before t rtv rc rb n v ee ir cs' callee argv setup
   fuel outs u.
  stmt_state_rel ctx func ce cx before t /\
  intcall_callee_exit func ce cx rtv rc rb n t (INL v) ee (IntRet ir cs') /\
  setup_callee callee argv t = SOME setup /\
  run_blocks fuel ctx callee setup = IntRet ir cs' /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs')) = SOME u /\
  EVERY (not_local_ptr ce before.scopes) outs /\
  immutable_alloca_sep func ce cx (ee with scopes := before.scopes) t /\
  (!name b sz aid off asz.
    local_region ce before.scopes t name b sz /\
    FLOOKUP t.vs_allocas aid = SOME (off,asz) /\ n <= aid ==>
    regions_disjoint b sz off asz) ==>
  stmt_state_rel ctx func ce cx (ee with scopes := before.scopes)
    (u with vs_inst_idx := SUC t.vs_inst_idx)
Proof
  simp[stmt_state_rel_inst_idx] >>
  metis_tac[tuple_immutable_intcall_return_restore_actual]
QED
