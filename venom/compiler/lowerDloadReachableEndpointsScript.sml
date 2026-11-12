Theory lowerDloadReachableEndpoints
Ancestors
  lowerDloadOwnership lowerDloadRuntimeDomain calleeTransport o1PassLift
  venomExecSemantics venomState finite_map

Theorem ld_step_static_endpoints:
  step_inst fuel C i s = OK t /\
  (!k b n. FLOOKUP s.vs_allocas k = SOME (b,n) ==>
     b+n <= s.vs_alloca_next) ==>
  !k b n. FLOOKUP t.vs_allocas k = SOME (b,n) ==>
     b+n <= t.vs_alloca_next
Proof
  Cases_on `i.inst_opcode = INVOKE`
  >- (simp[Once run_defs] >> strip_tac >>
      gvs[AllCaseEqs()] >>
      drule ld_bind_outputs_allocas >>
      drule bind_outputs_shared_fields >> rpt strip_tac >>
      gvs[merge_callee_state_def] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = ALLOCA`
  >- (gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
      metis_tac[ld_exec_alloca_static_endpoints]) >>
  strip_tac >> drule_all ld_step_nonallocation_fields >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ld_frame_reach_static_endpoints:
  !C fn s0 i s. frame_reach C fn s0 i s ==>
  (!k b n. FLOOKUP s0.vs_allocas k = SOME (b,n) ==>
     b+n <= s0.vs_alloca_next) ==>
  !k b n. FLOOKUP s.vs_allocas k = SOME (b,n) ==>
     b+n <= s.vs_alloca_next
Proof
  ho_match_mp_tac frame_reach_ind >> rpt conj_tac >> rpt strip_tac
  >- (drule ld_enters_block_allocation_fields >> strip_tac >> gvs[] >> metis_tac[]) 
  >- (qpat_x_assum `(_ ==> _)` (drule_then assume_tac) >>
      gvs[] >> metis_tac[ld_step_static_endpoints]) >>
  qpat_x_assum `(_ ==> _)` (drule_then assume_tac) >>
  drule ld_enters_block_allocation_fields >> strip_tac >> gvs[] >>
  metis_tac[ld_step_static_endpoints]
QED

Theorem ld_stack_origin_frame_endpoint:
  ld_stack_origin vs C stk fn s0 /\ vs.vs_allocas = FEMPTY /\
  frame_reach C fn s0 i s /\
  FLOOKUP s.vs_allocas k = SOME (b,n) ==>
  b+n <= s.vs_alloca_next
Proof
  strip_tac >> drule_all ld_stack_origin_empty_allocas >> strip_tac >>
  drule ld_frame_reach_static_endpoints >> simp[] >>
  disch_then drule >> simp[]
QED
