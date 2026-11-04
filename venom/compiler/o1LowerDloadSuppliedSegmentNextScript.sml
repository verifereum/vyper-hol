Theory o1LowerDloadSuppliedSegmentNext
Ancestors
  o1LowerDloadSuppliedSegmentResources o1LowerDloadSuppliedSegmentTransport
  o1LowerDloadSuppliedSegmentControl o1LowerDloadJointRelation
  o1LowerDloadOccurrence o1LowerDloadReadiness o1LowerDloadRawBridge
  o1LowerDloadOccurrenceHeadroom o1LowerDloadJointScalar
  o1LowerDloadEnvironment o1LowerDloadShared o1LowerDloadOpaque
  o1PassContract lowerDloadDefs ptrDiscipline contextCodegenRel
  venomExecSemantics venomExecProps venomWf venomInst venomState
  irSupply list finite_map words

Theorem ld_dloadbytes_successor_shape[local]:
  wf_function fn /\ fn_inst_wf fn /\ active_inst fn inst s /\
  inst.inst_opcode = DLOADBYTES /\ step_inst fuel C inst s = OK s1 ==>
  ?dst src sz p x z inst2.
    inst.inst_operands = [dst;src;sz] /\ inst.inst_outputs = [] /\
    eval_operand dst s = SOME p /\ eval_operand src s = SOME x /\
    eval_operand sz s = SOME z /\
    s1 = write_memory_with_expansion (w2n p)
      (TAKE (w2n z) (DROP (w2n x) s.vs_data_section ++ REPLICATE (w2n z) 0w)) s /\
    active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `inst_wf inst` by
    (fs[wf_function_def, fn_inst_wf_def, active_inst_def] >> metis_tac[MEM_EL]) >>
  `inst.inst_outputs = []` by gvs[inst_wf_def] >>
  `~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `s1.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  drule_all ld_nonterminator_successor >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
