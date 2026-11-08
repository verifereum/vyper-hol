Theory fnAliasInvPhi
Ancestors
  fnFrameStepsPhi fnPlanPrefix stackPlanGen

(* The value boundary depends on planner provenance, not assembly execution. *)
Theorem phi_provenance_final_alias:
  !base fn bb pred entry source final ra lo last dfg.
  phi_run_context fn bb pred entry source final /\
  phi_stack_provenance base pred entry
    (collect_phis bb.bb_instructions) [] last /\
  generated_plan_state_wf_marked base entry /\
  dfg = dfg_build_function fn /\
  (!op v. (MEM op entry.ps_stack \/ op IN FDOM entry.ps_spilled) /\
    ~(MEM op entry.ps_stack /\ ?inst. MEM inst (collect_phis bb.bb_instructions) /\
      resolve_phi pred inst.inst_operands = SOME op) /\
    (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
    ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
  (!at. MEM at entry.ps_stack \/ at IN FDOM entry.ps_spilled ==>
    operand_val (frame_view fn ra source) lo at =
    operand_val (frame_view fn ra source) lo (normalize_operand dfg [] at)) ==>
  !at. MEM at last.ps_stack \/ at IN FDOM last.ps_spilled ==>
    operand_val (frame_view fn ra final) lo at =
    operand_val (frame_view fn ra final) lo (normalize_operand dfg [] at)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac >>
  drule_all phi_provenance_final_resident >> disch_then DISJ_CASES_TAC
  >- (irule phi_eval_preserves_frame_alias >>
      qexistsl_tac [`collect_phis bb.bb_instructions`, `source`] >>
      gvs[phi_run_context_def] >>
      rpt strip_tac >>
      `~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))` by
        (qpat_x_assum `!op v. _` irule >> qexists_tac `at` >> simp[]) >>
      gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
      metis_tac[livenessProofsTheory.collect_phis_mem]) >>
  pop_assum strip_assume_tac >> gvs[] >>
  `ssa_form fn` by gvs[phi_run_context_def, codegen_ready_fn_def] >>
  `MEM inst (fn_insts fn)` by
    (gvs[phi_run_context_def] >>
     metis_tac[allocaRemapSSATheory.mem_fn_insts_intro,
       livenessProofsTheory.collect_phis_mem]) >>
  `inst.inst_opcode = PHI` by
    metis_tac[phi_codegen_inst_shape, phi_run_context_def] >>
  metis_tac[phi_output_normalize_self]
QED
