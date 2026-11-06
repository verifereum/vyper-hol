Theory lowerDloadReachableAlloca
Ancestors
  contextRawReachable contextCodegenRel lowerDloadOwnership
  venomMemProps venomMemDefs venomExecProofs venomExecSemantics calleeTransport

Theorem ld_raw_reachable_alloca_inv:
  !vs0 ctx fn inst s.
    raw_reachable vs0 ctx fn inst s ==> (alloca_inv vs0 ==> alloca_inv s)
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac
  >- (rpt strip_tac >> drule ld_enters_block_allocation_fields >> strip_tac >>
      gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
      metis_tac[])
  >- (rpt strip_tac >> `alloca_inv s'` by metis_tac[alloca_inv_step_inst] >>
      gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
      metis_tac[])
  >- (rpt strip_tac >> `alloca_inv s'` by metis_tac[alloca_inv_step_inst] >>
      drule ld_enters_block_allocation_fields >> strip_tac >>
      gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
      metis_tac[]) >>
  rpt strip_tac >> drule ld_enters_block_allocation_fields >> strip_tac >>
  gvs[setup_callee_def, AllCaseEqs()] >>
  irule alloca_inv_empty >> simp[]
QED

Theorem ld_annotated_alloca_inv:
  !vs0 C astk k L AP AG tn fn inst s.
    ld_annotated_reachable vs0 C astk k L AP AG tn fn inst s ==>
    alloca_inv s /\ (!f. MEM f astk ==> alloca_inv f.lf_state)
Proof
  ho_match_mp_tac ld_annotated_reachable_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> simp[] >>
      irule alloca_inv_empty >> simp[])
  >- (rpt strip_tac >>
      `alloca_inv s'` by metis_tac[alloca_inv_step_inst] >>
      gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
      metis_tac[])
  >- (rpt strip_tac >>
      `alloca_inv s'` by metis_tac[alloca_inv_step_inst] >>
      drule ld_enters_block_allocation_fields >> strip_tac >>
      gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
      metis_tac[])
  >- (rpt strip_tac >> gvs[] >>
      drule ld_enters_block_allocation_fields >> strip_tac >>
      gvs[setup_callee_def, AllCaseEqs()] >>
      irule alloca_inv_empty >> simp[]) >>
  rpt strip_tac >> gvs[] >>
  drule ld_bind_outputs_allocas >> strip_tac >>
  drule bind_outputs_shared_fields >> strip_tac >>
  gvs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
      adopt_return_fmp_allocas] >> metis_tac[]
QED
