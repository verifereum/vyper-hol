(* Allocation bounds along counted normal execution paths. *)
Theory bodyIntCallJointPurePath
Ancestors
  intCallFrame fragGasMode fragGasPath venomExecProofs venomExecSemantics
  venomState fragExec venomMemProps allocaFrontierBound venomInst

Theorem gas_path_edge_allocas_above:
  gas_path_edge ctx func s n (OK u) /\ allocas_above lo s ==>
  allocas_above lo u
Proof
  rw[gas_path_edge_def] >> gvs[exit_result_def]
  >- (drule step_inst_allocas_above >>
      disch_then (qspecl_then [`fuel`, `ctx`, `inst`] mp_tac) >>
      simp[result_allocas_above_def] >> strip_tac >>
      gvs[allocas_above_def] >> metis_tac[])
  >- (drule step_inst_allocas_above >>
      disch_then (qspecl_then [`fuel`, `ctx`, `inst`] mp_tac) >>
      simp[result_allocas_above_def] >> strip_tac >>
      drule eval_phis_preserves_alloca_fields >>
      strip_tac >> gvs[allocas_above_def] >> metis_tac[])
  >- (drule step_inst_allocas_above >>
      disch_then (qspecl_then [`fuel`, `ctx`, `inst`] mp_tac) >>
      simp[result_allocas_above_def]) >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[exit_result_def]
QED

Theorem gas_path_allocas_above:
  !ctx func s n r. gas_path ctx func s n r ==>
    !lo u. r = OK u /\ allocas_above lo s ==> allocas_above lo u
Proof
  ho_match_mp_tac gas_path_ind >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >> gvs[] >>
      first_x_assum irule >> simp[] >>
      metis_tac[gas_path_edge_allocas_above]) >>
  rpt strip_tac >> gvs[exit_result_def]
QED

Theorem gas_marked_path_allocas_above:
  gas_marked_path memory ctx func s n (OK u) /\ allocas_above lo s ==>
  allocas_above lo u
Proof
  strip_tac >> drule gas_marked_path_exec >>
  strip_tac >> drule gas_path_allocas_above >> simp[]
QED

Theorem normal_step_alloca_next_mono:
  step_inst fuel ctx inst s = OK u ==> s.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (drule_all step_inst_invoke_alloca_fields >> simp[]) >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (irule step_inst_alloca_alloca_next_mono >>
      qexistsl_tac [`ctx`, `fuel`, `inst`] >> simp[is_alloca_op_def]) >>
  `step_inst_base inst s = OK u` by metis_tac[step_inst_non_invoke] >>
  `u.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[step_inst_base_preserves_alloca_next] >> simp[]
QED

Theorem gas_path_edge_alloca_next_mono:
  gas_path_edge ctx func s n (OK u) ==> s.vs_alloca_next <= u.vs_alloca_next
Proof
  rw[gas_path_edge_def] >> gvs[exit_result_def]
  >- metis_tac[normal_step_alloca_next_mono]
  >- (drule eval_phis_preserves_alloca_fields >> strip_tac >>
      gvs[] >> metis_tac[normal_step_alloca_next_mono])
  >- metis_tac[normal_step_alloca_next_mono] >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[exit_result_def]
QED

Theorem gas_path_alloca_next_mono:
  !ctx func s n r. gas_path ctx func s n r ==>
    !u. r = OK u ==> s.vs_alloca_next <= u.vs_alloca_next
Proof
  ho_match_mp_tac gas_path_ind >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >> gvs[] >>
      drule gas_path_edge_alloca_next_mono >> strip_tac >>
      decide_tac) >>
  rpt strip_tac >> gvs[exit_result_def]
QED

Theorem gas_marked_path_alloca_next_mono:
  gas_marked_path memory ctx func s n (OK u) ==>
  s.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >> drule gas_marked_path_exec >>
  strip_tac >> drule gas_path_alloca_next_mono >> simp[]
QED
