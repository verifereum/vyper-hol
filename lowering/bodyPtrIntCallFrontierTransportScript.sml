Theory bodyPtrIntCallFrontierTransport
Ancestors bodyPtrIntCallFrontier bodyPtrIntCallAllocation
  bodyPtrIntCallConfinement allocaFrontierBound allocaBudgetProps
  venomMemProps fragGasPathPtr venomExecSemantics venomExecProofs
  venomState fragExec arithmetic

Theorem intcall_step_frontier_mono:
  step_inst fuel ctx inst s = OK t ==>
  s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (drule_all step_inst_invoke_alloca_fields >> simp[]) >>
  `step_inst_base inst s = OK t` by fs[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (drule_all step_inst_base_alloca_effect >>
      Cases_on `inst.inst_id IN FDOM s.vs_allocas` >> simp[]) >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[step_inst_base_preserves_alloca_next] >> simp[]
QED

Theorem intcall_edge_frontier_mono:
  gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' (OK t) ==>
  s.vs_alloca_next <= t.vs_alloca_next
Proof
  rw[gas_path_ptr_edge_def] >> gvs[exit_result_def]
  >- metis_tac[intcall_step_frontier_mono]
  >- (drule eval_phis_preserves_alloca_fields >> strip_tac >>
      drule intcall_step_frontier_mono >> simp[]) >>
  simp[jump_to_def] >> metis_tac[intcall_step_frontier_mono]
QED

Theorem intcall_path_frontier_mono:
  gas_path_ptr D lo ctx fn PG G tn s n G' tn' (OK t) ==>
  s.vs_alloca_next <= t.vs_alloca_next
Proof
  `!D lo ctx fn PG G tn s n G' tn' r.
     gas_path_ptr D lo ctx fn PG G tn s n G' tn' r ==>
     !t. r = OK t ==> s.vs_alloca_next <= t.vs_alloca_next`
    suffices_by metis_tac[] >>
  ho_match_mp_tac gas_path_ptr_ind >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >> gvs[] >>
      drule intcall_edge_frontier_mono >>
      decide_tac) >>
  rpt strip_tac >> gvs[exit_result_def]
QED

Theorem intcall_path_protected_frontier:
  stmt_state_rel ctx func cenv cx es s0 /\
  gas_path_ptr D lo ctx func PG G0 tn0 s0 n G tn (OK s) ==>
  !a. s.vs_alloca_next <= a ==>
      a NOTIN intcall_protected cenv es sa s0
Proof
  strip_tac >> drule intcall_protected_below_frontier >>
  drule intcall_path_frontier_mono >>
  metis_tac[LESS_EQ_TRANS]
QED

Theorem intcall_path_protected_setup:
  stmt_state_rel ctx func cenv cx es s0 /\
  gas_path_ptr D lo ctx func PG G0 tn0 s0 n G tn (OK s) /\
  setup_callee callee args s = SOME cs ==>
  intcall_alloc_outside (intcall_protected cenv es sa s0) cs
Proof
  strip_tac >> irule intcall_alloc_setup >>
  metis_tac[intcall_path_protected_frontier]
QED
