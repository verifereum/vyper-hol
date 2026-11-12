Theory lowerDloadRuntimeDomain
Ancestors
  lowerDloadOwnership lowerDloadScratchFreshness venomMemProofs
  ptrDiscipline finite_map pred_set venomExecSemantics venomState venomInst
  contextRawReachable contextCodegenRel o1PassLift list
  lowerDloadReachability

Theorem ld_step_alloca_domain:
  step_inst fuel C i s = OK t ==>
  FDOM t.vs_allocas SUBSET
    (FDOM s.vs_allocas UNION (if i.inst_opcode = ALLOCA then {i.inst_id} else {}))
Proof
  Cases_on `i.inst_opcode = INVOKE`
  >- (simp[Once run_defs] >> strip_tac >>
      gvs[AllCaseEqs()] >>
      drule ld_bind_outputs_allocas >>
      simp[merge_callee_state_def]) >>
  simp[step_inst_non_invoke] >> strip_tac >>
  Cases_on `i.inst_opcode = ALLOCA`
  >- (gvs[step_inst_base_def, exec_alloca_def, AllCaseEqs(), update_var_def] >>
      SET_TAC[]) >>
  `t.vs_allocas = s.vs_allocas` by
    metis_tac[venomMemProofsTheory.step_inst_base_preserves_allocas] >> simp[]
QED

Theorem ld_active_alloca_id_member[local]:
  active_inst fn i s /\ i.inst_opcode = ALLOCA ==>
  i.inst_id IN set (MAP (\j. j.inst_id)
    (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts fn)))
Proof
  simp[active_inst_def, fn_insts_def, MEM_MAP, MEM_FILTER, MEM_FLAT] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[EL_MEM, o1PassContractTheory.fn_insts_blocks_MEM]
QED

Theorem ld_frame_alloca_domain:
  !C fn s0 i s. frame_reach C fn s0 i s ==>
  FDOM s.vs_allocas SUBSET
    (FDOM s0.vs_allocas UNION
     set (MAP (\j. j.inst_id) (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts fn))))
Proof
  ho_match_mp_tac frame_reach_strongind >> rpt conj_tac >> rpt strip_tac
  >- (drule ld_enters_block_allocation_fields >> simp[])
  >- (drule frame_reach_active >> strip_tac >>
      drule ld_step_alloca_domain >> strip_tac >>
      Cases_on `i.inst_opcode = ALLOCA`
      >- (drule_all ld_active_alloca_id_member >> strip_tac >>
          gvs[] >> ASM_SET_TAC[]) >>
      gvs[] >> ASM_SET_TAC[]) >>
  drule frame_reach_active >> strip_tac >>
  drule ld_step_alloca_domain >> strip_tac >>
  drule ld_enters_block_allocation_fields >> strip_tac >>
  Cases_on `i.inst_opcode = ALLOCA`
  >- (drule_all ld_active_alloca_id_member >> strip_tac >>
      gvs[] >> ASM_SET_TAC[]) >>
  gvs[] >> ASM_SET_TAC[]
QED

Theorem ld_frame_alloca_exclusion:
  frame_reach C fn s0 i s /\
  DISJOINT cap (FDOM s0.vs_allocas) /\
  DISJOINT cap (set (MAP (\j. j.inst_id)
    (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts fn)))) ==>
  DISJOINT cap (FDOM s.vs_allocas)
Proof
  strip_tac >> drule ld_frame_alloca_domain >> ASM_SET_TAC[]
QED

Theorem ld_frame_scratch_cap_exclusion:
  frame_reach C fn s0 i s /\
  DISJOINT
    (set (MAP (\j. j.inst_id) (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts fn'))) DIFF
     set (MAP (\j. j.inst_id) (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts fn))))
    (FDOM s0.vs_allocas) ==>
  DISJOINT
    (set (MAP (\j. j.inst_id) (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts fn'))) DIFF
     set (MAP (\j. j.inst_id) (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts fn))))
    (FDOM s.vs_allocas)
Proof
  strip_tac >> drule ld_frame_alloca_domain >> ASM_SET_TAC[]
QED

Theorem ld_stack_origin_empty_allocas:
  ld_stack_origin vs C stk fn s0 /\ vs.vs_allocas = FEMPTY ==>
  s0.vs_allocas = FEMPTY
Proof
  simp[Once ld_stack_origin_cases] >> rpt strip_tac >>
  gvs[setup_callee_def, AllCaseEqs()]
QED

Theorem ld_stack_origin_saved_domains:
  !vs C stk fn s0. ld_stack_origin vs C stk fn s0 ==>
  vs.vs_allocas = FEMPTY ==>
  EVERY (\f. FDOM f.cf_state.vs_allocas SUBSET
    set (MAP (\j. j.inst_id)
      (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts f.cf_fn)))) stk
Proof
  ho_match_mp_tac ld_stack_origin_strongind >> rpt conj_tac >> rpt strip_tac
  >- simp[] >>
  drule_all ld_stack_origin_empty_allocas >> strip_tac >>
  drule ld_frame_alloca_domain >> simp[]
QED

Theorem ld_reachable_alloca_domain:
  o1_ctx_shape C /\ vs.vs_allocas = FEMPTY /\
  frame_reachable vs C stk PG G tn fn inst s ==>
  FDOM s.vs_allocas SUBSET
    set (MAP (\j. j.inst_id) (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts fn)))
Proof
  strip_tac >> drule_all ld_frame_reachable_prefix >> strip_tac >>
  drule_all ld_stack_origin_empty_allocas >> strip_tac >>
  drule ld_frame_alloca_domain >> simp[]
QED

Theorem ld_reachable_saved_alloca_domains:
  o1_ctx_shape C /\ vs.vs_allocas = FEMPTY /\
  frame_reachable vs C stk PG G tn fn inst s ==>
  EVERY (\f. FDOM f.cf_state.vs_allocas SUBSET
    set (MAP (\j. j.inst_id)
      (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts f.cf_fn)))) stk
Proof
  strip_tac >> drule_all ld_frame_reachable_prefix >> strip_tac >>
  drule_all ld_stack_origin_saved_domains >> simp[]
QED

Theorem ld_reachable_scratch_cap_exclusion:
  o1_ctx_shape C /\ vs.vs_allocas = FEMPTY /\
  frame_reachable vs C stk PG G tn fn inst s ==>
  DISJOINT
    (set (MAP (\j. j.inst_id) (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts fn'))) DIFF
     set (MAP (\j. j.inst_id) (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts fn))))
    (FDOM s.vs_allocas)
Proof
  strip_tac >> drule_all ld_reachable_alloca_domain >> ASM_SET_TAC[]
QED
