Theory lowerDloadReachableFloor
Ancestors
  lowerDloadFrameFloor o1PassLift ptrDiscipline venomExecSemantics
  venomState finite_map lowerDloadOwnership calleeTransport

Theorem ld_step_floor_total:
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  step_inst fuel C i s = OK t ==>
  allocas_from lo t /\ lo <= t.vs_alloca_next
Proof
  Cases_on `i.inst_opcode = INVOKE`
  >- (simp[Once run_defs] >> strip_tac >>
      gvs[AllCaseEqs()] >>
      drule ld_bind_outputs_allocas >>
      drule bind_outputs_shared_fields >> rpt strip_tac >>
      gvs[allocas_from_def, merge_callee_state_def] >> metis_tac[]) >>
  metis_tac[ld_step_floor]
QED

Theorem ld_frame_reach_floor:
  !C fn s0 i s. frame_reach C fn s0 i s ==>
  !lo. allocas_from lo s0 /\ lo <= s0.vs_alloca_next ==>
    allocas_from lo s /\ lo <= s.vs_alloca_next
Proof
  ho_match_mp_tac frame_reach_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac
  >- metis_tac[ld_enters_block_floor]
  >- (first_x_assum drule >> simp[] >> strip_tac >>
      drule_all ld_step_floor_total >> strip_tac >>
      simp[allocas_from_def] >> metis_tac[allocas_from_def]) >>
  first_x_assum drule >> simp[] >> strip_tac >>
  drule_all ld_step_floor_total >> strip_tac >>
  metis_tac[ld_enters_block_floor]
QED

Theorem ld_frame_reach_fixed_prefix_exclusion:
  frame_reach C fn s0 i s /\
  allocas_from lo s0 /\ lo <= s0.vs_alloca_next /\
  ((FLOOKUP s.vs_allocas k = NONE /\ p = s.vs_alloca_next) \/
   FLOOKUP s.vs_allocas k = SOME (p,n)) ==>
  !a. a < lo ==> a < p
Proof
  strip_tac >> drule_all ld_frame_reach_floor >>
  simp[allocas_from_def] >> rpt strip_tac >>
  res_tac >> decide_tac
QED
