(*
 * The planner's stack at a join block's entry.
 *
 * TOP-LEVEL (CHEATED, a piece):
 *   lineage_entry_join_stack — the lineage entry state of a join is a
 *                              dead_stack_marker prefix followed by exactly
 *                              the edge's live-in variables
 *)

Theory fnPlanLineageJoin
Ancestors
  fnLineageInv fnPlanLineage stackPlanGen stackPlanTypes livenessDefs dfgDefs cfgDefs

(* Used by fnFrameStepsPhi for phi_prefix_frame_sim: the PHI prefix reads
   pred's PHI operands from the top of the stack, and nothing below them
   may be a stale variable whose value the PHIs change.

   Why it should hold: every predecessor of a join ends in a JMP
   (block_entries_ready), whose plan reorders the stack so that it ends in
   the target's live-in variables (join_reached).  Below them only
   dead_stack_marker entries remain: the planner pops dead outputs,
   consumes an operand at its last use, and clean_stack_plan pops or marks
   dead what a single-predecessor block inherits but doesn't need.  This is
   the static lineage_state invariant the comment on
   fnPlanLineage$lineage_state_block_plan describes (a marker prefix, then
   distinct variables that together are the live set at the edge).

   The second conjunct is the PHI prefix's freshness: no stack or spill
   entry, other than a stack entry the prefix consumes (a PHI operand
   selected from pred), is or normalizes to an output of the block.  The
   only PHI operands on the stack are pred-edge sources (other-edge
   operands are not live out of pred, phi_block_ready); the JMP restores
   every target operand (do_restore deletes it from the spill map) and
   release_dead_spills frees the dead ones, so what stays spilled is a
   live-in non-PHI variable, whose definition (and its ASSIGN root's)
   strictly dominates the block. *)
Theorem lineage_entry_join_stack:
  !liveness dfg cfg fn ch growth spill_base lbl_ctr pred bb ps.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    LENGTH (cfg_preds_of cfg bb.bb_label) <> 1 /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred bb.bb_label ps ==>
    (?pre. ps.ps_stack = pre ++ MAP Var (input_vars_from pred bb.bb_instructions
                                         (live_vars_at liveness bb.bb_label 0)) /\
          EVERY (\op. op = dead_stack_marker) pre) /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
            ~(MEM op ps.ps_stack /\
              ?inst. MEM inst (collect_phis bb.bb_instructions) /\
                     resolve_phi pred inst.inst_operands = SOME op) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions)))
Proof
  cheat
QED
