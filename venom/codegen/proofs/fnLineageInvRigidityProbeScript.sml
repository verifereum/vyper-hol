Theory fnLineageInvRigidityProbe
Ancestors fnLineageInvSuffixCompare

(* Cross-decision diagnostic ledger, E0225 (probe source/build evidence is
   retained in the dossier, not as duplicate specialized cleanup facts).

   Actual lineage_step has two successful generate_block_plan runs of the
   same block and same full emitted code. One starts at a DFS state; one
   starts at the lineage state with arbitrary cleanup height/promise.
   lineage_state_dfs_fields gives the remaining DFS fields, but equality
   of incoming stack cores/spills is an induction obligation, not a
   consequence of emitted-code equality.

   Entry: initialization supplies equal stacks/spills; prepare_params_plan
   must be replayed before the ordinary suffix interface can be applied.
   Inactive singleton: cleanup is identity, so incoming common core and
   equal non-bookkeeping fields suffice for normalized suffix comparison.
   Active singleton, same effective decision: use
   clean_stack_plan_decision_coherence. It supplies common variable cores
   and allocation/spill agreement. Height/promise can remain independent.
   Join: use successful predecessor provenance and the native PHI common
   core interface, not equality of incoming variable names. The successor
   DFS fields must be spliced first. Then normalized suffix comparison
   handles separate cleanup height/promise.

   Active singleton, opposite decisions: three checked EVAL experiments
   (arbitrary query tables, not analyzed-function counterexamples) gave:
   - stack [x], layout [x], inputs []: elide emits [], leaves [marker];
     pop emits [SOPop 1], leaves [].
   - stack [x;y], layout [x;y], inputs [x]: retained empty; both emit
     [SOPop 1] and leave [x], despite opposite decisions.
   - stack [x;y], layout [x;y], inputs [y]: retained prefix [x]; elide
     emits [] and leaves [marker;y]; pop emits [SOSwap 1; SOPop 1]
     and leaves [y]. Thus equality of decisions is NOT necessary for
     common suffix cores, and is not recoverable in the retained-empty case.

   Residual bridge: given analyzed readiness/reachability, exact incoming
   live inventory on both runs, canonical resource budgets, common variable
   core, equality after erasing stack/height/promise, and two successful
   block runs with identical full code, prove equal filtered output stacks
   and equal output spill/allocation/label/growth fields. Do not require
   equal effective cleanup decisions. This is not established here.

   Full-block decomposition leaves clean_ops_L ++ inst_ops_L =
   clean_ops_D ++ inst_ops_D after cancelling the common label/parameter
   prefix. Neither clean chunk nor its length is known equal. Deep
   popmany_plan invokes do_swap, which can allocate temporary slots, so
   common variable core alone does not prove equal allocation fields.
   This allocation difference is the next interface to inspect, before
   using normalized suffix comparison across opposite cleanup decisions.

   Both actual successful runs independently imply their revert guards
   false; reconstruction of a new successful run instead needs equality
   of inst_ops to transport revert_block_spills, not just full code.
*)

(* Deep allocator diagnostic, E0226 and subsequent checked EVAL probe:
   names = [x0;...;x17], layout all names, successor inputs [x1;...;x17],
   singleton successor and branching predecessor. Only x0 is dead.
   Promised cleanup marks x0 and keeps the remaining order. Popping uses
   depth-17 swap, then pop: the resulting stack is [x17;x1;...;x16],
   NOT [x1;...;x17]. The popped durable spill map is empty. Thus opposite
   decisions need not even give the same filtered stack core.

   With init_spill_alloc 0, marking leaves the allocator unchanged;
   popping leaves next_offset=576 and free_slots=[0;32;...;544]. The next
   allocation returns 0 versus 544 respectively. With that sufficient
   free list initially present and next_offset=576, marking preserves it;
   popping reverses it, without highwater growth. Subsequent allocations
   return 544 versus 0. Equal free sets do not mean equal allocation order.

   Resource interface audit:
   - doSwapSim.spill_alloc_n_free_layout_wf_arbitrary preserves layout for
     the SAME durable map through allocate/free of arbitrary items.
   - doSwapSim.spill_alloc_n_temporary_layout additionally gives temporary
     offset distinctness/separation, bounds, base equality and highwater
     monotonicity, but no allocator identity or cross-run map relation.
     Neither theorem is needed as a new import here; no frame-level facts
     have been copied or made a planner dependency.
   - fnLineageInvSpillReplay.plan_slots_bounded_occupied_addresses needs
     each replacement offset to occur in the original map.
   - spill_alloc_layout_wf_occupied_addresses needs that same inclusion
     AND injectivity of the replacement map. Domain equality is insufficient.
   - fnLineageInvOwnerOrigin.spill_alloc_layout_wf_extension requires exact
     free-list equality as well as base equality and monotone highwater.
     It applies along the DFS owner extension, not across these cleanups.

   Strongest supported splice contract: given DFS state D already satisfying
   slot bounds and layout, lineage map m may replace D.ps_spilled if every
   offset in m occurs in D.ps_spilled and m is injective. This proves both
   resource conjuncts without equal operand names or allocators across runs.
   The occupied-address inclusion remains a reachability/replay obligation;
   independent layout safety of the two runs cannot discharge it. Full-code
   equality has not been used to cancel unequal cleanup/suffix chunks.
   These arbitrary query-table examples do not refute the frozen theorem.
*)
