(*
 * Static facts about a lineage state (fnPlanLineage): the planner state a
 * run-time path reaches at a block's entry.  The block-entry prefix lemmas
 * (fnFrameSteps$phi_prefix_frame_sim, fnFrameSinglePred) and the block
 * body (fnBlockBody) need them of the state they start from.
 *
 * TOP-LEVEL:
 *   lineage_state_static - CHEATED: the state is well formed (repeated
 *                          dead_stack_marker slots allowed), and nothing on
 *                          its stack or in its spill map stands for a
 *                          variable the block itself defines
 *)

Theory fnLineageStatic
Ancestors
  fnPlanPrefix fnPlanLineage stackPlanGen stackPlanTypes dfgDefs

(* Why the second conjunct should hold: in SSA, a variable on the stack at
   lbl's entry was defined on the path there.  Since the last join on that
   path, whose incoming JMP reorders the stack to the join's live inputs,
   every block dominates the next, so each such definition strictly
   dominates lbl, and so do the ASSIGN sources normalize_operand follows.
   None of them is therefore an output of lbl's own instructions.  The
   first conjunct: the planner keeps generated_plan_state_wf_marked through
   each block plan, and a lineage entry takes the stack and spill map of
   the predecessor's plan with the successor's DFS allocator. *)
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
            normalize_operand dfg [] op = Var v ==>
            ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions)))
Proof
  cheat
QED
