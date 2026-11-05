(* Reachable allocation frontiers, including internal and oracle calls. *)
Theory lowerDloadFrontier
Ancestors
  venomMemProps venomMemProofs venomExecProofs contextRawReachable
  contextCodegenRel list venomState venomExecSemantics venomInst

Theorem ld_foldl_outputs_frontier[local]:
  !xs s. (FOLDL (\s (out,v). update_var out v s) s xs).vs_alloca_next =
         s.vs_alloca_next
Proof
  Induct >> simp[] >> Cases_on `h` >> simp[update_var_def]
QED

Theorem ld_bind_outputs_frontier:
  bind_outputs outs vals s = SOME q ==>
  q.vs_alloca_next = s.vs_alloca_next
Proof
  simp[bind_outputs_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[] >> simp[ld_foldl_outputs_frontier]
QED

Theorem ld_step_frontier_mono:
  step_inst fuel C inst s = OK q ==>
  s.vs_alloca_next <= q.vs_alloca_next
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (gvs[Once step_inst_def, AllCaseEqs()] >>
      drule ld_bind_outputs_frontier >>
      Cases_on `ret.iret_adopt_fmp` >>
      simp[adopt_return_fmp_def, merge_callee_state_def]) >>
  `step_inst_base inst s = OK q` by gvs[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (irule step_inst_alloca_alloca_next_mono >>
      qexistsl_tac [`C`, `fuel`, `inst`] >> simp[is_alloca_op_def]) >>
  `q.vs_alloca_next = s.vs_alloca_next` suffices_by simp[] >>
  irule step_inst_base_preserves_alloca_next >>
  qexists_tac `inst` >> simp[]
QED

Theorem ld_enters_block_frontier:
  enters_block fn s q ==> q.vs_alloca_next = s.vs_alloca_next
Proof
  simp[enters_block_def] >> rpt strip_tac >>
  drule eval_phis_preserves_alloca_fields >> simp[]
QED

Theorem ld_setup_callee_frontier:
  setup_callee fn args s = SOME q ==> q.vs_alloca_next = s.vs_alloca_next
Proof
  simp[setup_callee_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem ld_raw_reachable_frontier:
  !vs0 C fn inst s. raw_reachable vs0 C fn inst s ==>
    vs0.vs_alloca_next <= s.vs_alloca_next
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt strip_tac
  >- (drule ld_enters_block_frontier >> simp[])
  >- (drule ld_step_frontier_mono >> simp[])
  >- (drule ld_step_frontier_mono >>
      drule ld_enters_block_frontier >> simp[])
  >> drule ld_setup_callee_frontier >>
  drule ld_enters_block_frontier >> simp[]
QED
