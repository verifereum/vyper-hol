(* Allocation growth retained by actual normal execution paths. *)
Theory extcallProtFramePath
Ancestors
  abiEncoderWindowContract allocaFrontierBound fragGasMode fragGasPath
  fragExec venomExecSemantics venomExecProofs venomMemProofs venomState
  finite_map list arithmetic

Theorem normal_step_allocation_frame[local]:
  step_inst fuel ctx inst s = OK t ==>
  window_alloca_growth s t /\
  (!i r. FLOOKUP s.vs_allocas i = SOME r ==>
         FLOOKUP t.vs_allocas i = SOME r)
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (drule_all step_inst_invoke_alloca_fields >> strip_tac >>
      simp[window_alloca_growth_fields]) >>
  `step_inst_base inst s = OK t` by metis_tac[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[Once step_inst_base_def, exec_alloca_def, AllCaseEqs()] >>
      simp[window_alloca_growth_def, update_var_def, FLOOKUP_UPDATE] >>
      rpt strip_tac >> Cases_on `i = inst.inst_id` >> gvs[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    metis_tac[step_inst_base_preserves_alloca_fields] >>
  simp[window_alloca_growth_fields]
QED

Theorem gas_path_edge_allocation_frame[local]:
  gas_path_edge ctx func s n (OK t) ==>
  window_alloca_growth s t /\
  (!i r. FLOOKUP s.vs_allocas i = SOME r ==>
         FLOOKUP t.vs_allocas i = SOME r)
Proof
  simp[gas_path_edge_def] >> strip_tac >> gvs[exit_result_def]
  >- (drule normal_step_allocation_frame >> strip_tac >>
      gvs[window_alloca_growth_def] >> metis_tac[])
  >- (drule normal_step_allocation_frame >> strip_tac >>
      drule eval_phis_preserves_alloca_fields >> strip_tac >>
      gvs[window_alloca_growth_def] >> metis_tac[])
  >- (drule normal_step_allocation_frame >> simp[]) >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[exit_result_def]
QED

Theorem gas_path_allocation_frame[local]:
  !ctx func s n r. gas_path ctx func s n r ==>
  !t. r = OK t ==>
  window_alloca_growth s t /\
  (!i v. FLOOKUP s.vs_allocas i = SOME v ==>
         FLOOKUP t.vs_allocas i = SOME v)
Proof
  ho_match_mp_tac gas_path_ind >> rpt conj_tac
  >- simp[window_alloca_growth_refl]
  >- (rpt strip_tac >> gvs[] >>
      drule gas_path_edge_allocation_frame >> strip_tac >>
      metis_tac[window_alloca_growth_trans]) >>
  rpt strip_tac >> gvs[exit_result_def]
QED

Theorem gas_path_window_alloca_growth:
  gas_path ctx func s n (OK t) ==> window_alloca_growth s t
Proof
  metis_tac[gas_path_allocation_frame]
QED

Theorem gas_path_allocas_preserved:
  gas_path ctx func s n (OK t) ==>
  !i r. FLOOKUP s.vs_allocas i = SOME r ==>
        FLOOKUP t.vs_allocas i = SOME r
Proof
  metis_tac[gas_path_allocation_frame]
QED

Theorem gas_marked_path_window_alloca_growth:
  gas_marked_path memory ctx func s n (OK t) ==> window_alloca_growth s t
Proof
  metis_tac[gas_marked_path_exec, gas_path_window_alloca_growth]
QED

Theorem gas_marked_path_allocas_preserved:
  gas_marked_path memory ctx func s n (OK t) ==>
  !i r. FLOOKUP s.vs_allocas i = SOME r ==>
        FLOOKUP t.vs_allocas i = SOME r
Proof
  metis_tac[gas_marked_path_exec, gas_path_allocas_preserved]
QED
