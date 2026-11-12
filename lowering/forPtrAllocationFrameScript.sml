(* Successful caller-visible execution extends the existing allocation map. *)
Theory forPtrAllocationFrame
Ancestors
  fragGasPathPtr abiAllocationHistory venomMemProps venomExecProofs
  venomExecSemantics venomState venomInst finite_map list

Theorem exec_alloca_old_allocations:
  exec_alloca inst s allocsz = OK t ==>
  !aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
    FLOOKUP t.vs_allocas aid = SOME b
Proof
  simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[update_var_def, FLOOKUP_UPDATE] >>
  Cases_on `aid = inst.inst_id` >> gvs[]
QED

Theorem step_inst_old_allocations:
  step_inst fuel ctx inst s = OK t ==>
  !aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
    FLOOKUP t.vs_allocas aid = SOME b
Proof
  strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (drule_all abi_alloca_history_invoke >> simp[]) >>
  `step_inst_base inst s = OK t` by gvs[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
      simp[step_inst_base_opcode_eqs, AllCaseEqs()] >> strip_tac >>
      drule exec_alloca_old_allocations >> simp[]) >>
  `t.vs_allocas = s.vs_allocas` by
    (irule step_inst_base_preserves_allocas >> metis_tac[]) >>
  simp[]
QED

Theorem gas_path_ptr_edge_old_allocations:
  gas_path_ptr_edge D lo ctx fn PG G tn s n H tm (OK t) ==>
  !aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
    FLOOKUP t.vs_allocas aid = SOME b
Proof
  rw[gas_path_ptr_edge_def] >> gvs[fragExecTheory.exit_result_def]
  >- (drule step_inst_old_allocations >> simp[]) 
  >- (drule eval_phis_preserves_alloca_fields >> strip_tac >>
      drule step_inst_old_allocations >> simp[])
  >- simp[jump_to_def] >>
  metis_tac[step_inst_old_allocations]
QED

Theorem gas_path_ptr_old_allocations:
  !D lo ctx fn PG G tn s n H tm r.
    gas_path_ptr D lo ctx fn PG G tn s n H tm r ==>
    !t aid b. r = OK t /\ FLOOKUP s.vs_allocas aid = SOME b ==>
      FLOOKUP t.vs_allocas aid = SOME b
Proof
  ho_match_mp_tac gas_path_ptr_ind >> rpt conj_tac
  >- simp[]
  >- (rpt strip_tac >> gvs[] >>
      drule gas_path_ptr_edge_old_allocations >>
      disch_then drule >> strip_tac >> first_x_assum irule >> simp[]) >>
  rpt strip_tac >> gvs[] >>
  drule gas_path_ptr_edge_old_allocations >> simp[]
QED

Theorem gas_outcome_ptr_allocation_frame:
  gas_outcome_ptr D tops (ctx,fn) PG source (es,s,G,tn) Q R ==>
  gas_outcome_ptr D tops (ctx,fn) PG source (es,s,G,tn)
    (\res ee H tm t. Q res ee H tm t /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b)) R
Proof
  simp_tac bool_ss [gas_outcome_ptr_def, gas_summary_ptr_at_def] >>
  rpt strip_tac >> qexists_tac `marks`
  >- (disj1_tac >>
      drule gas_path_ptr_old_allocations >> strip_tac >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[])
  >- (disj1_tac >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[]) >>
  disj2_tac >> metis_tac[]
QED
