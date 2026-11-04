Theory concretizePtrActivationSupport
Ancestors concretizePtrRootCover concretizePtrFrameOrigins concretizePtrClosure
  concretizePtrRuntimeOrigins pointerClosure pointerConfinedDefs
  ptrDiscipline venomInst finite_map pred_set list
  concretizePtrAllocationOrigins venomMemProps venomExecSemantics
  ptrDisciplineEmptyTaint venomState

Theorem ptr_frame_roots_extend:
  (!aid p. FLOOKUP A aid = SOME p ==> FLOOKUP B aid = SOME p) ==>
  ptr_frame_site_roots fn A PG site SUBSET ptr_frame_site_roots fn B PG site
Proof
  simp[SUBSET_DEF, ptr_frame_site_roots_def] >> metis_tac[]
QED

Theorem ptr_frame_support_extend:
  (!aid p. FLOOKUP A aid = SOME p ==> FLOOKUP B aid = SOME p) /\
  ptr_site_supported (pointer_derived_vars fn (ptr_frame_site_roots fn A PG site)) G site ==>
  ptr_site_supported (pointer_derived_vars fn (ptr_frame_site_roots fn B PG site)) G site
Proof
  strip_tac >>
  `pointer_derived_vars fn (ptr_frame_site_roots fn A PG site) SUBSET
   pointer_derived_vars fn (ptr_frame_site_roots fn B PG site)` by
    (irule ptr_derived_mono >> simp[ptr_frame_site_roots_finite] >>
     metis_tac[ptr_frame_roots_extend]) >>
  fs[ptr_site_supported_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem ptr_site_support_restrict:
  ptr_site_supported X G site ==> ptr_site_supported X (DRESTRICT G keys) site
Proof
  simp[ptr_site_supported_def, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem ptr_step_allocas_extend:
  inst.inst_opcode <> DALLOCA /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel ctx inst s = OK s' ==>
  !aid p. FLOOKUP s.vs_allocas aid = SOME p ==>
    FLOOKUP s'.vs_allocas aid = SOME p
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
      metis_tac[exec_alloca_lookup_preserved]) >>
  `~is_alloca_op inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def]) >>
  metis_tac[step_inst_non_alloca_preserves_allocas]
QED

Theorem ptr_frame_current_table_step:
  ptr_site_supported
    (pointer_derived_vars fn (ptr_frame_site_roots fn s.vs_allocas PG site)) G site /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode <> DALLOCA /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = OK s' ==>
  ptr_site_supported
    (pointer_derived_vars fn (ptr_frame_site_roots fn s'.vs_allocas PG site))
    (step_prov PG G inst s') site
Proof
  strip_tac >> irule ptr_frame_site_step >> simp[] >>
  irule ptr_frame_support_extend >>
  goal_assum (drule_at Any) >> metis_tac[ptr_step_allocas_extend]
QED

Theorem ptr_frame_current_table_entry:
  ptr_site_supported
    (pointer_derived_vars fn (ptr_frame_site_roots fn s.vs_allocas PG site)) G site /\
  enters_block fn s s1 ==>
  ptr_site_supported
    (pointer_derived_vars fn (ptr_frame_site_roots fn s1.vs_allocas PG site))
    (entry_prov fn s G) site
Proof
  strip_tac >> drule enters_block_allocas >> strip_tac >> simp[] >>
  metis_tac[ptr_frame_site_entry]
QED

Theorem ptr_return_allocas:
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state saved ended)) = SOME s' ==>
  s'.vs_allocas = saved.vs_allocas
Proof
  strip_tac >> drule bind_outputs_allocation_frame >>
  simp[merge_callee_state_allocas]
QED
