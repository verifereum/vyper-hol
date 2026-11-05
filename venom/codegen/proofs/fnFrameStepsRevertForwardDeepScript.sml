(*
 * revert_forward_frame_sim_deep: fnFrameSteps' revert_forward_frame_sim
 * for a planner state with cleanup markers.  A cleanup elision
 * (clean_stack_plan's mark_dead_stack) leaves dead_stack_marker in several
 * stack slots, so the block induction keeps generated_plan_state_wf_marked
 * (fnPlanPrefix), not generated_plan_state_wf.  The other fnFrameDeep
 * relaxations don't apply: revert_forward_frame_sim's ownership premise
 * already allows any depth, and it has no prefix_spill_wf premise (its
 * plan has no SOSpill or SORestore at all).
 *
 * TOP-LEVEL:
 *   revert_forward_frame_sim_deep
 *)

Theory fnFrameStepsRevertForwardDeep
Ancestors
  fnFrameStepsRevertForward fnPlanPrefix

(* fnFrameStepsRevertForward's entry lemmas need only spill separation,
   which the marked invariant gives as well. *)
Theorem rf_spills_separated_entry_marked:
  !base ps. generated_plan_state_wf_marked base ps ==> rf_spills_separated ps
Proof
  rpt strip_tac >> fs[generated_plan_state_wf_marked_def] >>
  drule doSwapSimTheory.spill_alloc_layout_wf_spilled_separated >>
  simp[rf_spills_separated_def]
QED

(* Used in the block induction at a revert forwarding's RETURNDATACOPY, as
   revert_forward_frame_sim, from the planner state the induction keeps.

   Why it should hold: as revert_forward_frame_sim.  The segment's code
   has no spill or restore, so the spill map is only read through
   fn_frame_inv; generated_plan_state_wf's ALL_DISTINCT ps_stack is only
   needed to find an operand's stack slot, and stack_get_depth finds the
   topmost copy whatever the marker slots below it, which hold no
   variable and are never an operand (dead_stack_marker is no operand of
   a codegen_ready_fn instruction). *)
Theorem revert_forward_frame_sim_deep:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn bb i j base ps vs as ops
   ps_end ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\
    codegen_ready_fn fn /\ opaque_use_ok fn /\
    lookup_block vs.vs_current_bb fn.fn_blocks = SOME bb /\
    revert_forward_pair bb i j /\ vs.vs_inst_idx = i /\
    LENGTH (get_params bb.bb_instructions) <= i /\
    EVERY (\inst. EVERY (\op. ~is_label_operand op) inst.inst_operands)
      (DROP i bb.bb_instructions) /\
    generated_plan_state_wf_marked base ps /\
    (!k inst op.
       i <= k /\ get_instruction bb k = SOME inst /\
       MEM op (compute_operands inst) /\ is_var_operand op /\
       (!k' inst' x. i <= k' /\ k' < k /\ get_instruction bb k' = SOME inst' /\
                     op = Var x ==> ~MEM x inst'.inst_outputs) ==>
       MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_block_insts_plan liveness dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) (i - LENGTH (get_params bb.bb_instructions))
      (DROP i bb.bb_instructions) ps = SOME (ops, ps_end) /\
    (!off. ~MEM (SORestore off) ops /\ ~MEM (SOSpill off) ops) /\
    (!name. MEM (AsmOp name) (execute_plan cp.cp_initial_fmp ops) ==>
            IS_SOME (evm_opcode_byte name)) /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !a vs'. exec_block fuel ctx bb vs = Abort a vs' ==>
      ?n as'.
        ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
         (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
        venom_asm_terminal_rel vs' as'
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac >>
  drule rf_spills_separated_entry_marked >> strip_tac >>
  drule_all rf_entry_forward_abort >> simp[]
QED
