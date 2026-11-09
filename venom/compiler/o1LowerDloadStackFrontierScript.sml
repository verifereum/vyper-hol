Theory o1LowerDloadStackFrontier
Ancestors
  o1LowerDloadOccurrence venomMemProps venomMemProofs venomExecProofs
  allocaFrontierBound localPtrsProps ptrDiscipline
  contextCodegenRel venomExecSemantics venomInstProofs1 venomInst list

Theorem ld_step_frontier_mono:
  step_inst fuel C inst s = OK s' /\ inst.inst_opcode <> INVOKE ==>
  s.vs_alloca_next <= s'.vs_alloca_next
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (irule step_inst_alloca_alloca_next_mono >>
      qexistsl_tac [`C`, `fuel`, `inst`] >> simp[is_alloca_op_def]) >>
  `step_inst_base inst s = OK s'` by gvs[step_inst_non_invoke] >>
  `s'.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[step_inst_base_preserves_alloca_next] >> simp[]
QED

Theorem ld_enters_block_frontier:
  enters_block fn s s' ==> s'.vs_alloca_next = s.vs_alloca_next
Proof
  simp[enters_block_def] >> rpt strip_tac >> gvs[] >>
  drule eval_phis_preserves_alloca_fields >> simp[]
QED

Theorem ld_setup_callee_frontier:
  setup_callee fn args s = SOME s' ==> s'.vs_alloca_next = s.vs_alloca_next
Proof
  simp[setup_callee_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem ld_return_frontier:
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state caller callee)) = SOME s' ==>
  s'.vs_alloca_next = caller.vs_alloca_next
Proof
  strip_tac >>
  qspec_then `\s. s.vs_alloca_next` mp_tac bind_outputs_preserves >>
  simp[venomStateTheory.update_var_def] >> disch_then drule >>
  Cases_on `ret.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem ld_occ_stack_frontiers:
  !vs C stk PG G tn fn inst s n a U B HP H.
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H ==>
  !i j. i <= j /\ j < LENGTH (s::MAP (\f. f.cf_state) stk) ==>
    (EL j (s::MAP (\f. f.cf_state) stk)).vs_alloca_next <=
    (EL i (s::MAP (\f. f.cf_state) stk)).vs_alloca_next
Proof
  ho_match_mp_tac occ_frame_reachable_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> simp[] >> rpt strip_tac >>
      `i = 0 /\ j = 0` by decide_tac >> gvs[])
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume ld_occ_stack_frontiers[next]:
  rpt gen_tac >> strip_tac >>
  `s.vs_alloca_next <= s'.vs_alloca_next` by
    (irule ld_step_frontier_mono >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  namedCases_on `i` ["", "ii"]
  >- (namedCases_on `j` ["", "jj"] >> gvs[] >>
      first_x_assum (qspecl_then [`0`, `SUC jj`] mp_tac) >>
      simp[] >> decide_tac) >>
  namedCases_on `j` ["", "jj"] >> gvs[] >>
  first_x_assum (qspecl_then [`SUC ii`, `SUC jj`] mp_tac) >> simp[]
QED

Resume ld_occ_stack_frontiers[block]:
  rpt gen_tac >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  `s.vs_alloca_next <= s'.vs_alloca_next` by
    (irule ld_step_frontier_mono >> metis_tac[]) >>
  `s''.vs_alloca_next = s'.vs_alloca_next` by
    metis_tac[ld_enters_block_frontier] >>
  rpt gen_tac >> strip_tac >>
  namedCases_on `i` ["", "ii"]
  >- (namedCases_on `j` ["", "jj"] >> gvs[] >>
      first_x_assum (qspecl_then [`0`, `SUC jj`] mp_tac) >>
      simp[] >> decide_tac) >>
  namedCases_on `j` ["", "jj"] >> gvs[] >>
  first_x_assum (qspecl_then [`SUC ii`, `SUC jj`] mp_tac) >> simp[]
QED
Resume ld_occ_stack_frontiers[call]:
  rpt gen_tac >> strip_tac >>
  `s''.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[ld_setup_callee_frontier, ld_enters_block_frontier] >>
  rpt gen_tac >> strip_tac >>
  namedCases_on `i` ["", "ii"]
  >- (namedCases_on `j` ["", "jj"] >> gvs[] >>
      first_x_assum (qspecl_then [`0`, `jj`] mp_tac) >> simp[]) >>
  namedCases_on `j` ["", "jj"] >> gvs[] >>
  first_x_assum (qspecl_then [`ii`, `jj`] mp_tac) >> simp[]
QED
Resume ld_occ_stack_frontiers[ret]:
  rpt gen_tac >> strip_tac >>
  `s'.vs_alloca_next = f.cf_state.vs_alloca_next` by
    (irule ld_return_frontier >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >>
  simp[] >>
  namedCases_on `i` ["", "ii"] >> namedCases_on `j` ["", "jj"] >>
  gvs[]

QED
Finalise ld_occ_stack_frontiers

Theorem ld_occ_saved_frontiers:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H ==>
  EVERY (\f. f.cf_state.vs_alloca_next <= s.vs_alloca_next) stk
Proof
  strip_tac >> drule ld_occ_stack_frontiers >>
  disch_then (qspec_then `0` assume_tac) >>
  simp[EVERY_EL] >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC n'` mp_tac) >> simp[EL_MAP]
QED

Theorem ld_frame_reachable_alloca_inv:
  !vs C stk PG G tn fn inst s.
  frame_reachable vs C stk PG G tn fn inst s ==>
  vs.vs_allocas = FEMPTY ==>
  alloca_inv s /\ EVERY (\f. alloca_inv f.cf_state) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> strip_tac >> simp[] >>
      drule enters_block_alloca_fields >> strip_tac >>
      irule alloca_inv_empty >> simp[])
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume ld_frame_reachable_alloca_inv[next]:
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  `alloca_inv s'` by metis_tac[alloca_inv_step_inst] >>
  irule alloca_inv_fields >> qexists `s'` >> simp[]
QED

Resume ld_frame_reachable_alloca_inv[block]:
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  `alloca_inv s'` by metis_tac[alloca_inv_step_inst] >>
  drule enters_block_alloca_fields >> strip_tac >>
  irule alloca_inv_fields >> qexists `s'` >> simp[]
QED

Resume ld_frame_reachable_alloca_inv[call]:
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  drule enters_block_alloca_fields >> strip_tac >>
  irule alloca_inv_empty >>
  gvs[setup_callee_def, AllCaseEqs()]
QED

Resume ld_frame_reachable_alloca_inv[ret]:
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[] >>
  qspec_then `\s. (s.vs_allocas, s.vs_alloca_next)` mp_tac
    bind_outputs_preserves >>
  simp[venomStateTheory.update_var_def] >> disch_then drule >>
  Cases_on `ret.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, merge_callee_state_def] >> strip_tac >>
  irule alloca_inv_fields >> qexists `f.cf_state` >> simp[]
QED
Finalise ld_frame_reachable_alloca_inv

Theorem ld_frame_reachable_current_alloca_inv:
  frame_reachable vs C stk PG G tn fn inst s /\ vs.vs_allocas = FEMPTY ==>
  alloca_inv s
Proof
  metis_tac[ld_frame_reachable_alloca_inv]
QED

Theorem ld_frame_reachable_saved_alloca_inv:
  frame_reachable vs C stk PG G tn fn inst s /\ vs.vs_allocas = FEMPTY ==>
  EVERY (\f. alloca_inv f.cf_state) stk
Proof
  metis_tac[ld_frame_reachable_alloca_inv]
QED

Theorem ld_frame_reachable_initial_frontier:
  !vs C stk PG G tn fn inst s.
  frame_reachable vs C stk PG G tn fn inst s ==>
  vs.vs_alloca_next <= s.vs_alloca_next /\
  EVERY (\f. vs.vs_alloca_next <= f.cf_state.vs_alloca_next) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      drule ld_enters_block_frontier >> simp[])
  >- (rpt gen_tac >> strip_tac >> simp[] >>
      `s.vs_alloca_next <= s'.vs_alloca_next` by
        (irule ld_step_frontier_mono >> metis_tac[]) >> decide_tac)
  >- (rpt gen_tac >> strip_tac >> simp[] >>
      `inst.inst_opcode <> INVOKE` by
        (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
      `s.vs_alloca_next <= s'.vs_alloca_next` by
        (irule ld_step_frontier_mono >> metis_tac[]) >>
      drule ld_enters_block_frontier >> decide_tac)
  >- (rpt gen_tac >> strip_tac >> simp[] >>
      drule ld_setup_callee_frontier >> strip_tac >>
      drule ld_enters_block_frontier >> simp[])
  >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule ld_return_frontier >> simp[]
QED

Theorem ld_frame_reachable_current_initial_frontier:
  frame_reachable vs C stk PG G tn fn inst s ==>
  vs.vs_alloca_next <= s.vs_alloca_next
Proof
  metis_tac[ld_frame_reachable_initial_frontier]
QED
