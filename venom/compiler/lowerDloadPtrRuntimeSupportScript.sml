(* Single-run allocation table footprints; no paired simulation assumptions. *)
Theory lowerDloadPtrRuntimeSupport
Ancestors
  lowerDloadPtrEntry lowerDloadPtrBudget venomMemProps venomExecSemantics
  venomState venomInst ptrDiscipline ctxLookupAgreeHelpers finite_map pred_set list

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

Theorem dload_frame_alloca_support:
  !vs ctx stk PG G tn fn inst s.
  frame_reachable vs ctx stk PG G tn fn inst s ==>
  vs.vs_allocas = FEMPTY ==>
  FDOM s.vs_allocas SUBSET set (MAP (\i. i.inst_id)
    (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts fn))) /\
  EVERY (\c. FDOM c.cf_state.vs_allocas SUBSET set (MAP (\i. i.inst_id)
    (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts c.cf_fn)))) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> strip_tac >>
      drule dload_enters_block_allocations >> simp[])
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume dload_frame_alloca_support[next]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all dload_step_alloca_footprint >> strip_tac >>
  `MEM inst (fn_insts fn)` by
    (qpat_assum `active_inst fn inst s`
       (mp_then (Pos last) mp_tac EVERY_active_inst) >>
     disch_then (qspec_then `\i. MEM i (fn_insts fn)` mp_tac) >>
     simp[EVERY_MEM]) >>
  simp[] >> Cases_on `inst.inst_opcode = ALLOCA` >>
  gvs[SUBSET_DEF, MEM_MAP, MEM_FILTER] >> metis_tac[]
QED
Resume dload_frame_alloca_support[block]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule dload_terminator_not_invoke >> strip_tac >>
  drule_all dload_step_alloca_footprint >> strip_tac >>
  drule dload_enters_block_allocations >> strip_tac >>
  `inst.inst_opcode <> ALLOCA` by
    (strip_tac >> gvs[is_terminator_def]) >>
  gvs[] >> metis_tac[SUBSET_TRANS]
QED
Resume dload_frame_alloca_support[call]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule dload_setup_callee_allocas >> strip_tac >>
  drule dload_enters_block_allocations >> strip_tac >> simp[]
QED
Resume dload_frame_alloca_support[ret]:
  rpt gen_tac >> strip_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule dload_return_allocas >> strip_tac >> gvs[]
QED
Finalise dload_frame_alloca_support

Theorem dload_frame_alloca_outside_subset:
  vs.vs_allocas = FEMPTY /\ frame_reachable vs ctx stk PG G tn fn inst s ==>
  FDOM s.vs_allocas DIFF A SUBSET set (MAP (\i. i.inst_id)
    (FILTER (\i. i.inst_opcode = ALLOCA /\ i.inst_id NOTIN A) (fn_insts fn)))
Proof
  strip_tac >> drule_all dload_frame_alloca_support >> strip_tac >>
  gvs[SUBSET_DEF, MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

Theorem dload_frame_scratch_budget:
  vs.vs_allocas = FEMPTY /\ frame_reachable vs ctx stk PG G tn gn inst t /\
  lower_dload_function_supply q fn = (gn,q') /\
  (!i. MEM i (fn_insts fn) ==> i.inst_id IN A) ==>
  FINITE (FDOM t.vs_allocas DIFF A) /\
  CARD (FDOM t.vs_allocas DIFF A) <=
    LENGTH (FILTER (\i. i.inst_opcode = DLOAD) (fn_insts fn))
Proof
  strip_tac >> irule dload_function_scratch_budget >>
  drule_all dload_frame_alloca_outside_subset >>
  disch_then (qspec_then `A` assume_tac) >> metis_tac[]
QED
