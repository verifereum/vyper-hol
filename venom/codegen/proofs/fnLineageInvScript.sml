(*
 * The planner's stack inventory along a lineage edge.
 *
 * TOP-LEVEL (CHEATED, a piece):
 *   lineage_entry_inventory — entering a block from pred, the planner state
 *                             is well formed (dead_stack_marker slots
 *                             repeated), every other stack slot and every
 *                             spilled operand is a variable live at the end
 *                             of pred, and every such variable is on the
 *                             stack or spilled
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
   live set).  Nothing is live at the function's entry
   (fnLiveDefDom$live_def_dominates at index 0 of the entry block), which
   starts the lower half.

   The JMP reorder stays in range: before reordering, the JMP's plan
   restores every spilled target (restore_spilled_plan), and reorder_one
   keeps the stack length.  So the stack has at least LENGTH targets slots,
   and no do_swap depth LENGTH targets - 1 - i passes its bottom, provided
   the targets (MAP Var (input_vars_from pred ..)) are distinct and each is
   on the stack or spilled at the JMP.  Distinctness comes from readiness,
   not from the reorder's result: shared incoming PHI operands are
   rejected, PHI slots are injective, phi_uses_disjoint keeps PHI inputs
   apart from the other live-ins, input_vars_from emits each PHI index at
   most once, and live_vars_at is duplicate free (live_update dedupes like
   Python's OrderedSet.update; livenessDefs$live_update_ALL_DISTINCT,
   propagated through the liveness fixpoint).  The rest is the coverage
   half of this induction.

   Spill layout: the lineage state takes ps_alloc from the successor's DFS
   state, which extends the alloc after pred's DFS plan
   (dfs_block_state_owner_alloc_origin: same free list, larger next
   offset).  So spill_alloc_layout_wf follows once the lineage spill map is
   the DFS one.  Carry that as an invariant over lineage_state: ps_spilled
   is the DFS state's, and ps_stack is the DFS stack up to the
   dead_stack_marker prefix (and, at a join, PHI inputs from the other
   predecessor).  At a join both spill maps are empty (the argument of
   fnFrameStepsPhi$phi_join_entry_spill_empty).  Within a block both runs
   emit the same ops, but release_dead_spills frees slots without emitting
   any, so the invariant must carry the spill map itself, not just the
   ops. *)
Theorem lineage_entry_inventory:
  !liveness dfg cfg ch growth spill_base lbl_ctr fn pred pred_bb succ ps.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    lookup_block pred fn.fn_blocks = SOME pred_bb /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred succ ps
    ==>
    generated_plan_state_wf_marked spill_base ps /\
    (!op. (MEM op ps.ps_stack /\ op <> dead_stack_marker) \/
          op IN FDOM ps.ps_spilled ==>
          ?v. op = Var v /\
              MEM v (live_vars_at liveness pred
                       (LENGTH pred_bb.bb_instructions))) /\
    !v. MEM v (live_vars_at liveness pred (LENGTH pred_bb.bb_instructions)) ==>
        MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled
Proof
  cheat
QED
