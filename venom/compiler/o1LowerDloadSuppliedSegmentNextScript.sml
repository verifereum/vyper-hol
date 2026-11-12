Theory o1LowerDloadSuppliedSegmentNext
Ancestors
  o1LowerDloadSuppliedSegmentResources o1LowerDloadSuppliedSegmentTransport
  o1LowerDloadSuppliedSegmentControl o1LowerDloadJointRelation
  o1LowerDloadOccurrence o1LowerDloadReadiness o1LowerDloadRawBridge
  o1LowerDloadOccurrenceHeadroom o1LowerDloadJointScalar
  o1LowerDloadScratchExtension
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

Theorem ld_joint_dloadbytes_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  mem_inv dload_offset_ok C vs /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode = DLOADBYTES /\ step_inst fuel C inst s = OK s1 ==>
  ?inst2 es t2 t3 fn' bb'.
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    TAKE 2 (DROP t.vs_inst_idx bb'.bb_instructions) = es /\ LENGTH es = 2 /\
    t.vs_inst_idx + 2 <= LENGTH bb'.bb_instructions /\
    step_inst fuel C' (EL 0 es) t = OK t2 /\
    step_inst fuel C' (EL 1 es) t2 = OK t3 /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t3 with vs_inst_idx := t.vs_inst_idx+2)
      n a U B HP (occurrence_step a HP H inst s1) sites X ts
Proof
  (* P4a in progress *) cheat
QED

Theorem ld_dload_successor_shape[local]:
  wf_function fn /\ fn_inst_wf fn /\ active_inst fn inst s /\
  inst.inst_opcode = DLOAD /\ step_inst fuel C inst s = OK s1 ==>
  ?off out x inst2.
    inst.inst_operands = [off] /\ inst.inst_outputs = [out] /\
    eval_operand off s = SOME x /\
    s1 = update_var out (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n x) s.vs_data_section ++ REPLICATE 32 0w))) s /\
    active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `inst_wf inst` by
    (fs[wf_function_def, fn_inst_wf_def, active_inst_def] >> metis_tac[MEM_EL]) >>
  `?off out. inst.inst_operands = [off] /\ inst.inst_outputs = [out]` by
    gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
  `~is_terminator inst.inst_opcode` by simp[is_terminator_def] >>
  `s1.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  drule_all ld_nonterminator_successor >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac (srw_ss()) [step_inst_base_opcode_eqs] >>
  simp[exec_read1_def, bind_outputs_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ld_joint_dload_next:
  ld_joint_boundary vs C C' lo D stk PG G tn fn inst s t
    n a U B HP H sites X ts /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  mem_inv dload_offset_ok C vs /\ mem_inv dload_headroom_ok C vs /\
  callee_first names C.ctx_functions /\ ptr_discipline lo C vs /\
  opaque_use_ok fn /\ active_inst fn inst s /\
  inst.inst_opcode = DLOAD /\ step_inst fuel C inst s = OK s1 ==>
  ?inst2 es t1 t2 t3 t4 fn' bb' X1.
    lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
    lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb' /\
    TAKE 4 (DROP t.vs_inst_idx bb'.bb_instructions) = es /\ LENGTH es = 4 /\
    t.vs_inst_idx + 4 <= LENGTH bb'.bb_instructions /\
    step_inst fuel C' (EL 0 es) t = OK t1 /\
    step_inst fuel C' (EL 1 es) t1 = OK t2 /\
    step_inst fuel C' (EL 2 es) t2 = OK t3 /\
    step_inst fuel C' (EL 3 es) t3 = OK t4 /\
    ((FLOOKUP X (a,inst.inst_id) = NONE /\
      X1 = X |+ ((a,inst.inst_id),((EL 0 es).inst_id,t.vs_alloca_next))) \/
     (IS_SOME (FLOOKUP X (a,inst.inst_id)) /\ X1 = X)) /\
    ld_joint_boundary vs C C' lo D stk PG (step_prov PG G inst s1)
      (step_taint inst s s1 tn) fn inst2
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t4 with vs_inst_idx := t.vs_inst_idx+4)
      n a U B HP (occurrence_step a HP H inst s1) sites X1 ts
Proof
  (* P4a in progress *) cheat
QED
