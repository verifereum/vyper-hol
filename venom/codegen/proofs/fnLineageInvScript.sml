(*
 * The planner's stack inventory along a lineage edge.
 *
 * TOP-LEVEL (CHEATED, a piece):
 *   lineage_entry_inventory — entering a block from pred, the planner state
 *                             is well formed (dead_stack_marker slots
 *                             repeated) and every other stack slot and every
 *                             spilled operand is a variable live at the end
 *                             of pred
 *)

Theory fnLineageInv
Ancestors
  fnPlanPrefix fnPlanLineage stackPlanGen stackPlanTypes livenessDefs dfgDefs

(* Used by fnPlanLineageJoin (the join entry stack) and fnLineageStatic
   (freshness of a lineage state's stack).

   Why it should hold: the state is pred's plan run from a lineage state of
   pred.  The planner keeps a variable on the stack or in the spill map only
   while it is live: an operand's slot is consumed at its last use (a live
   one is duplicated first), a dead output is popped, release_dead_spills
   drops dead spill entries after every instruction, and clean_stack_plan
   pops or marks dead what a single-predecessor block inherits but doesn't
   need.  Consuming the right slots needs the converse as well: every live
   variable is on the stack or spilled, so the operand searches and
   reorders find each operand (the planner fails only on a JMP that misses
   its target stack, join_reached).  Hence an induction over lineage_state
   with the full inventory (a dead_stack_marker prefix, then distinct
   variables, disjoint from the spill map, that together with it are the
   live set), of which this is the upper half. *)
Theorem lineage_entry_inventory:
  !liveness dfg cfg ch growth spill_base lbl_ctr fn pred pred_bb succ ps.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    lookup_block pred fn.fn_blocks = SOME pred_bb /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred succ ps
    ==>
    generated_plan_state_wf_marked spill_base ps /\
    !op. (MEM op ps.ps_stack /\ op <> dead_stack_marker) \/
         op IN FDOM ps.ps_spilled ==>
         ?v. op = Var v /\
             MEM v (live_vars_at liveness pred
                      (LENGTH pred_bb.bb_instructions))
Proof
  cheat
QED
