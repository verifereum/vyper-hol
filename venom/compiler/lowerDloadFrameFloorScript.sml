Theory lowerDloadFrameFloor
Ancestors
  lowerDloadOwnership calleeTransport ptrDiscipline venomMemProps
  venomExecSemantics venomState finite_map

Theorem ld_exec_alloca_floor:
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ exec_alloca i s w = OK s' ==>
  allocas_from lo s' /\ lo <= s'.vs_alloca_next
Proof
  simp[exec_alloca_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[allocas_from_def, FLOOKUP_UPDATE, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem ld_step_floor:
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  step_inst fuel C i s = OK s' /\ i.inst_opcode <> INVOKE ==>
  allocas_from lo s' /\ lo <= s'.vs_alloca_next
Proof
  strip_tac >> Cases_on `i.inst_opcode = ALLOCA`
  >- (gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
      metis_tac[ld_exec_alloca_floor]) >>
  drule_all ld_step_nonallocation_fields >> strip_tac >>
  gvs[allocas_from_def] >> metis_tac[]
QED

Theorem ld_enters_block_floor:
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ enters_block fn s s' ==>
  allocas_from lo s' /\ lo <= s'.vs_alloca_next
Proof
  strip_tac >> drule ld_enters_block_allocation_fields >> strip_tac >>
  gvs[allocas_from_def] >> metis_tac[]
QED

Theorem ld_setup_callee_floor:
  setup_callee fn args caller = SOME child ==>
  allocas_from caller.vs_alloca_next child /\
  child.vs_alloca_next = caller.vs_alloca_next
Proof
  simp[setup_callee_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[allocas_from_def]
QED

Theorem ld_return_floor:
  allocas_from lo caller /\ lo <= caller.vs_alloca_next /\
  bind_outputs outs vals (merge_callee_state caller callee) = SOME bound ==>
  allocas_from lo (adopt_return_fmp ir bound) /\
  lo <= (adopt_return_fmp ir bound).vs_alloca_next
Proof
  strip_tac >> drule ld_bind_outputs_allocas >>
  drule bind_outputs_shared_fields >> rpt strip_tac >>
  gvs[allocas_from_def] >> metis_tac[]
QED
