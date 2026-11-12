Theory lowerDloadReachableFloor
Ancestors
  lowerDloadFrameFloor o1PassLift ptrDiscipline venomExecSemantics
  venomState finite_map lowerDloadOwnership calleeTransport venomInstProps venomInst

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

Theorem ld_step_frontier_floor:
  lo <= s.vs_alloca_next /\ step_inst fuel C i s = OK t ==>
  lo <= t.vs_alloca_next
Proof
  Cases_on `i.inst_opcode = INVOKE`
  >- (simp[Once run_defs] >> strip_tac >>
      gvs[AllCaseEqs()] >>
      drule bind_outputs_shared_fields >> rpt strip_tac >>
      gvs[merge_callee_state_def] >> metis_tac[]) >>
  Cases_on `i.inst_opcode = ALLOCA`
  >- (strip_tac >>
      `s.vs_alloca_next <= t.vs_alloca_next` by
        (irule venomMemPropsTheory.step_inst_alloca_next_mono >>
         goal_assum (drule_at Any) >>
         simp[is_terminator_def,is_ext_call_op_def]) >> decide_tac) >>
  metis_tac[ld_step_nonallocation_fields]
QED

Theorem ld_frame_reachable_frontier_floor:
  !vs0 C stk PG G tn fn i s.
    frame_reachable vs0 C stk PG G tn fn i s ==>
    !lo. lo <= vs0.vs_alloca_next ==>
      lo <= s.vs_alloca_next /\
      EVERY (\f. lo <= f.cf_state.vs_alloca_next) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume ld_frame_reachable_frontier_floor[entry]:
  rpt strip_tac >>
  drule ld_enters_block_allocation_fields >> simp[]
QED

Resume ld_frame_reachable_frontier_floor[next]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all ld_step_frontier_floor >> simp[]
QED

Resume ld_frame_reachable_frontier_floor[block]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all ld_step_frontier_floor >> strip_tac >>
  drule ld_enters_block_allocation_fields >> simp[]
QED

Resume ld_frame_reachable_frontier_floor[call]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule ld_setup_callee_floor >> strip_tac >>
  drule ld_enters_block_allocation_fields >> simp[]
QED

Resume ld_frame_reachable_frontier_floor[ret]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  drule bind_outputs_shared_fields >> rpt strip_tac >>
  gvs[merge_callee_state_def]
QED

Finalise ld_frame_reachable_frontier_floor

Theorem ld_ptr_reachable_frontier_floor:
  ptr_discipline lo C vs0 /\
  frame_reachable vs0 C stk PG G tn fn i s ==>
  lo <= s.vs_alloca_next
Proof
  strip_tac >> drule ld_frame_reachable_frontier_floor >>
  disch_then (qspec_then `lo` mp_tac) >>
  fs[ptr_discipline_def]
QED

Theorem ld_frame_reachable_allocas_floor:
  !vs0 C stk PG G tn fn i s.
    frame_reachable vs0 C stk PG G tn fn i s ==>
    !lo. allocas_from lo vs0 /\ lo <= vs0.vs_alloca_next ==>
      allocas_from lo s /\ EVERY (\f. allocas_from lo f.cf_state) stk
Proof
  ho_match_mp_tac frame_reachable_strongind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume ld_frame_reachable_allocas_floor[entry]:
  rpt strip_tac >>
  drule ld_enters_block_allocation_fields >> strip_tac >>
  gvs[allocas_from_def] >> first_assum ACCEPT_TAC
QED

Resume ld_frame_reachable_allocas_floor[next]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  drule ld_frame_reachable_frontier_floor >>
  disch_then (qspec_then `lo` mp_tac) >> simp[] >> strip_tac >>
  drule_all ld_step_floor_total >> strip_tac >>
  gvs[allocas_from_def] >> first_assum ACCEPT_TAC
QED

Resume ld_frame_reachable_allocas_floor[block]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  drule ld_frame_reachable_frontier_floor >>
  disch_then (qspec_then `lo` mp_tac) >> simp[] >> strip_tac >>
  drule_all ld_step_floor_total >> strip_tac >>
  drule_all ld_enters_block_floor >> simp[]
QED

Resume ld_frame_reachable_allocas_floor[call]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  drule ld_frame_reachable_frontier_floor >>
  disch_then (qspec_then `lo` mp_tac) >> simp[] >> strip_tac >>
  drule ld_setup_callee_floor >> strip_tac >>
  drule ld_enters_block_allocation_fields >> strip_tac >>
  gvs[allocas_from_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Resume ld_frame_reachable_allocas_floor[ret]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  drule ld_bind_outputs_allocas >> strip_tac >>
  gvs[allocas_from_def] >> metis_tac[]
QED

Finalise ld_frame_reachable_allocas_floor

Theorem ld_access_ok_raise_floor:
  access_ok l G fn i s /\ l <= L ==> access_ok L G fn i s
Proof
  rewrite_tac[access_ok_def] >> strip_tac >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  strip_tac >> first_x_assum drule >> strip_tac >>
  conj_tac >> rpt gen_tac >> disch_tac >>
  first_x_assum irule >> fs[] >>
  metis_tac[arithmeticTheory.LESS_EQ_LESS_TRANS]
QED

Theorem ld_ptr_discipline_raise_floor:
  ptr_discipline l C vs0 /\ l <= L /\ L <= vs0.vs_alloca_next /\
  allocas_from L vs0 ==> ptr_discipline L C vs0
Proof
  simp[ptr_discipline_def] >> strip_tac >>
  qexists_tac `P` >> simp[] >> rpt gen_tac >> strip_tac >>
  drule_all ld_frame_reachable_allocas_floor >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  metis_tac[ld_access_ok_raise_floor]
QED

Theorem ld_o1_src_inv_frontier_discipline:
  o1PassContract$o1_run_state_ok vs0 /\ o1PassContract$o1_src_inv D C vs0 ==>
  ptr_discipline vs0.vs_alloca_next C vs0
Proof
  strip_tac >>
  `allocas_from vs0.vs_alloca_next vs0` by
    (gvs[o1PassContractTheory.o1_run_state_ok_def,
         unitTransformDefsTheory.o1_initial_state_ok_def, allocas_from_def]) >>
  qpat_x_assum `o1PassContract$o1_src_inv D C vs0` mp_tac >>
  simp[o1PassContractTheory.o1_src_inv_def] >> strip_tac >>
  drule ld_ptr_discipline_raise_floor >>
  disch_then (qspec_then `vs0.vs_alloca_next` irule) >>
  gvs[ptr_discipline_def]
QED
