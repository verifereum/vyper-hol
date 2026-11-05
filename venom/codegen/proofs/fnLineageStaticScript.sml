(*
 * Static facts about a lineage state (fnPlanLineage): the planner state a
 * run-time path reaches at a block's entry.  The block-entry prefix lemmas
 * (fnFrameSteps$phi_prefix_frame_sim, fnFrameSinglePred) and the block
 * body (fnBlockBody) need them of the state they start from.
 *
 * TOP-LEVEL:
 *   lineage_state_static - CHEATED: the state is well formed (repeated
 *                          dead_stack_marker slots allowed), and nothing on
 *                          its stack or in its spill map but the block's
 *                          PHI sources stands for a variable the block
 *                          defines (nothing at all with one predecessor)
 *)

Theory fnLineageStatic
Ancestors
  fnPlanPrefix fnPlanLineage stackPlanGen stackPlanTypes livenessDefs dfgDefs

(* Why it should hold.  Freshness: a join's entry stack is its JMP
   reorder's target, the predecessor-side PHI sources and the live-in
   variables; a source may be an output of the join itself (a loop header
   x = phi(a, v) whose body defines v), hence the exclusion of the PHI
   operands.  A live-in variable's definition strictly dominates the
   block, and so do the ASSIGN sources normalize_operand follows, so none
   is an output of the block.  A block with one predecessor P is entered
   with P's live-out variables (and markers), whose definitions dominate P
   and so the block, PHI sources included.  Well-formedness: a join is
   entered by a JMP, after which the spill map is empty (restore_spilled_plan,
   release_dead_spills), so only the successor's DFS allocator matters; a
   single-predecessor block is entered with the predecessor's spill map,
   which the lineage run allocates as the DFS run does (the stacks differ
   only in a bottom prefix of dead_stack_marker slots). *)
Theorem lineage_state_static:
  !liveness dfg cfg ch growth spill_base lbl_ctr fn fn_ops ps_end lbl bb ps.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lineage_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps
    ==>
    generated_plan_state_wf_marked spill_base ps /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
            ~MEM op (FLAT (MAP (\inst. inst.inst_operands)
                              (collect_phis bb.bb_instructions))) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    (LENGTH (cfg_preds_of cfg lbl) <= 1 ==>
     !op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions)))
Proof
  cheat
QED
