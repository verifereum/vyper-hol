Theory fnPlanLineageLiveness
Ancestors
  stackPlanGen livenessConvergenceProofs
Libs
  livenessDefsTheory livenessBlockProofsTheory

Theorem analyzed_live_out_singleton:
  !fn pred succ pred_bb succ_bb.
    wf_function fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block pred fn.fn_blocks = SOME pred_bb /\
    lookup_block succ fn.fn_blocks = SOME succ_bb /\
    cfg_succs_of (cfg_analyze fn) pred = [succ] ==>
    set (live_vars_at (liveness_analyze fn) pred
      (LENGTH pred_bb.bb_instructions)) =
    set (input_vars_from pred succ_bb.bb_instructions
      (live_vars_at (liveness_analyze fn) succ 0))
Proof
  rpt strip_tac >> drule_all liveness_recompute_convergence >>
  simp[same_vars_set, liveness_instrs_def, liveness_out_def,
       liveness_edge_transfer_def, liveness_analyze_def, live_vars_at_def,
       dfHelperDefsTheory.list_union_def]
QED

Theorem analyzed_live_out_edge_subset:
  !fn pred succ pred_bb succ_bb.
    wf_function fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block pred fn.fn_blocks = SOME pred_bb /\
    lookup_block succ fn.fn_blocks = SOME succ_bb /\
    MEM succ (cfg_succs_of (cfg_analyze fn) pred) ==>
    set (input_vars_from pred succ_bb.bb_instructions
      (live_vars_at (liveness_analyze fn) succ 0)) SUBSET
    set (live_vars_at (liveness_analyze fn) pred
      (LENGTH pred_bb.bb_instructions))
Proof
  rpt strip_tac >> drule_all liveness_recompute_edge_subset >>
  simp[liveness_instrs_def, liveness_edge_transfer_def,
       liveness_analyze_def, live_vars_at_def]
QED

Theorem analyzed_live_out_jmp:
  !fn pred succ pred_bb succ_bb inst.
    codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block pred fn.fn_blocks = SOME pred_bb /\
    lookup_block succ fn.fn_blocks = SOME succ_bb /\
    pred_bb.bb_instructions <> [] /\ LAST pred_bb.bb_instructions = inst /\
    inst.inst_opcode = JMP /\ inst.inst_operands = [Label succ] ==>
    set (live_vars_at (liveness_analyze fn) pred
      (LENGTH pred_bb.bb_instructions)) =
    set (input_vars_from pred succ_bb.bb_instructions
      (live_vars_at (liveness_analyze fn) succ 0))
Proof
  rpt strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  irule analyzed_live_out_singleton >> simp[] >>
  qpat_x_assum `lookup_block pred _ = _` mp_tac >>
  simp[venomInstTheory.lookup_block_def] >>
  strip_tac >> drule FIND_SOME_MEM >> strip_tac >>
  drule_all cfgAnalysisPropsTheory.cfg_analyze_preserves_bb_succs >>
  Cases_on `pred_bb.bb_instructions` >>
  gvs[venomInstTheory.bb_succs_def, venomInstTheory.get_successors_def,
      venomInstTheory.is_terminator_def, venomStateTheory.get_label_def,
      listTheory.nub_def]
QED
