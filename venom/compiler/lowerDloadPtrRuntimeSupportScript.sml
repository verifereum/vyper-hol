(* Single-run allocation table footprints; no paired simulation assumptions. *)
Theory lowerDloadPtrRuntimeSupport
Ancestors
  lowerDloadPtrEntry lowerDloadPtrBudget venomMemProps venomExecSemantics
  venomState venomInst finite_map pred_set list

Theorem dload_step_alloca_footprint:
  i.inst_opcode <> INVOKE /\ step_inst fuel ctx i s = OK u ==>
  FDOM u.vs_allocas SUBSET FDOM s.vs_allocas UNION
    (if i.inst_opcode = ALLOCA then {i.inst_id} else {})
Proof
  strip_tac >>
  `step_inst_base i s = OK u` by metis_tac[step_inst_non_invoke] >>
  Cases_on `i.inst_opcode = ALLOCA`
  >- (gvs[step_inst_base_def, AllCaseEqs()] >>
      gvs[exec_alloca_def, AllCaseEqs(), update_var_def] >>
      simp[SUBSET_DEF]) >>
  `u.vs_allocas = s.vs_allocas` by
    metis_tac[step_inst_base_preserves_allocas] >> simp[]
QED

Theorem dload_setup_callee_allocas:
  setup_callee fn args s = SOME u ==> u.vs_allocas = FEMPTY
Proof
  simp[setup_callee_def] >> strip_tac >> gvs[]
QED

Theorem dload_bind_outputs_allocas:
  bind_outputs outs vals s = SOME u ==> u.vs_allocas = s.vs_allocas
Proof
  simp[bind_outputs_def] >> strip_tac >> gvs[] >>
  qid_spec_tac `s` >>
  qspec_tac (`ZIP (outs,vals)`, `pairs`) >>
  Induct >> simp[] >>
  rpt gen_tac >> PairCases_on `h` >> simp[update_var_def]
QED

Theorem dload_return_allocas:
  bind_outputs outs vals (adopt_return_fmp ret (merge_callee_state saved ended)) = SOME u ==>
  u.vs_allocas = saved.vs_allocas
Proof
  strip_tac >> drule dload_bind_outputs_allocas >>
  simp[merge_callee_state_def]
QED

Theorem dload_terminator_not_invoke:
  is_terminator op ==> op <> INVOKE
Proof
  Cases_on `op` >> simp[is_terminator_def]
QED
