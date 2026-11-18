(* Active-frame packets independent of entry-frame preparation. *)
Theory fnFramePrefixDriverPrep
Ancestors
  fnFramePrefix fnBlockBodySteps fnBlockBodyHelpers
  frameJointTransition frameJointRevert
  frameRel contextCodegenRel stackPlanGen asmSem venomExecSemantics venomInst venomState
  list rich_list arithmetic

Theorem active_frame_local_step_reloc:
  active_frame_plan_reloc lo rpolicy unit cpl prog fn s ast ra rest mem0 /\
  active_inst fn inst s /\ ~in_revert_forward fn s /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
  source_memory_reads_disjoint cpl inst s /\
  context_source_memory_writes_disjoint cpl inst s /\
  step_inst fuel unit.cu_context inst s = OK post ==>
  ?n ast1.
    asm_steps lo (build_offset_to_pc prog)
      prog n ast = AsmOK ast1 /\
    active_frame_plan_reloc lo rpolicy unit cpl prog fn
      (post with vs_inst_idx := SUC s.vs_inst_idx) ast1 ra rest mem0
Proof
  strip_tac >> Cases_on `inst.inst_opcode = GAS`
  >- (drule_all active_frame_gas_step_reloc >> simp[]) >>
  drule_all active_frame_ordinary_step_reloc >> simp[]
QED

Theorem active_frame_rf_entry_reloc:
  active_frame_plan_reloc lo rpolicy unit cpl prog fn s ast ra rest mem0 /\
  in_revert_forward fn s ==>
  ?bb stopidx.
    ALL_DISTINCT (fn_labels fn) /\
    joint_revert_suffix fn bb s.vs_inst_idx stopidx
      (JointConfig stk PG G tn fn inst s oms om hs h)
Proof
  rw[active_frame_plan_reloc_def] >>
  drule body_plan_inv_facts_reloc >> strip_tac >>
  `(!i j. revert_forward_pair bb i j ==> k <= i \/ j < k) /\
   s.vs_inst_idx = k /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    fs[body_plan_inv_reloc_def] >>
  `ALL_DISTINCT (fn_labels fn)` by
    fs[codegen_ready_fn_def, venomWfTheory.wf_function_def] >>
  fs[in_revert_forward_def, revert_forward_at_def] >>
  qexistsl_tac [`bb`, `j`] >> simp[joint_revert_suffix_def] >>
  fs[revert_forward_pair_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL,
    arithmeticTheory.LESS_IMP_LESS_OR_EQ, arithmeticTheory.NOT_LESS_EQUAL]
QED
