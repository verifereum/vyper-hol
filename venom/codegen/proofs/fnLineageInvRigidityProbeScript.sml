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

(* Complete-trace audit (not a proof of rigidity).

   Candidate consumer: PL is the lineage input after cleanup override, PD the
   predecessor DFS input, AL/AD their successful outputs. Given analyzed
   readiness/reachability, exact incoming inventories, a common incoming core
   (or native PHI correspondence), incoming spill and non-cleanup bookkeeping
   agreement, and generate_block_plan ... PL = SOME (ops,AL) together with
   generate_block_plan ... PD = SOME (ops,AD), seek
     (!x off. FLOOKUP AL.ps_spilled x = SOME off ==>
        ?y. FLOOKUP AD.ps_spilled y = SOME off)
   plus injectivity of AL.ps_spilled. These are desired obligations, not
   established implications. lineage_step supplies the same block/whole ops
   and two successes. Exact inventories, common core and incoming spill
   agreement remain induction producers; lineage_state_dfs_fields gives
   only the other DFS fields.

   Existing interfaces inspected (reuse, do not copy):
   - planAlign.apply_prefix_ops_append composes over APPEND;
     do_restore_ss_align needs nonoverlapping offsets; emit_one_input_ss_align
     also needs stack length<=15 and excludes INVOKE label input;
     do_swap_align covers only dist<=16.
   - mixedPrefixSim.apply_prefix_op records SOSpill ownership from TOS and
     chooses a mapped owner on SORestore. But SOEmit/SOPoke delegate to
     apply_simple_op, which ignores them. It is NOT a full source-output
     ownership observer. These theories have simulation/codegenRel ancestry;
     no new import or copied theorem is proposed. No frame theorem is used.
   - fnPlanPrefix.phi_release_dead_spills_domain restricts keys by live NAME.
     fnPlanLineageReplay.release_dead_spills_live_domain makes release identity
     only if every current key is already next-live. Exact pre-instruction
     inventory does not imply that: last-use inputs may die at this boundary.
   - fnPlanLineageInventory/Setup subset and resource preservation do not
     provide final same-trace occupied-address equality.

   Constructor/update accounting:
   SOSpill off says where TOS is written, not its source variable name.
   SORestore removes durable ownership in do_restore; deep do_swap instead
   uses temporary spills/restores while preserving the durable map. All
   written addresses therefore do not determine final durable occupancy.
   SOPoke includes PHI output names and generate_phi_plan updates the model;
   apply_simple_op ignores it. OFFSET emits label+offset but pushes Var output.
   Regular planning silently pops inputs/pushes named outputs before emission;
   SOEmit carries an opcode, not output names. INVOKE emits return/target
   labels and JUMP, with label-counter changes, not source output names.

   Silent release discriminator, checked by scratch computation: maps
   {live|->0} and {dead|->0}, same empty stack and allocator next=32/free=[],
   released with next=[live], leave respectively the first map/free list
   unchanged and the second map empty/free=[0]. They began with the same
   occupied address. Thus an address-only relation is not preserved through
   release. This is NOT a counterexample to the target or actual same-block
   consumer: the second map lacks exact live inventory. Boundary coverage
   tracks stack OR spill; it alone does not relate names at each address.

   Missing APPEND-compositional boundary: a source-aware relation must track
   stack cells and address owners, commute with explicit trace operations,
   identify matching next-live owners at silent deletion, and account for
   output creation/PHI renaming at source checkpoints. Required obligations:
   (1) initial ownership correspondence; (2) source-checkpoint alignment in
   equal complete code; (3) preservation through temporaries and release;
   (4) final occupied-address inclusion and injectivity. Incoming common core
   and spills may supply (1); equal whole code does not yet supply (2).
   No inspected theorem supplies (2)-(4) with unequal cleanup chunks. No
   interpreter is defined: that route needs approved interface probes, not
   another normalization wrapper or cancellation of unequal APPEND prefixes.

   Height discriminator: assuming safe nontruncating full-trace alignment,
   equal traces preserve the difference of initial stack lengths. Raw prefix
   semantics does not supply full alignment at SOEmit. Even if available,
   exact distinct inventory gives final length = marker_count + live_count
   - spill_domain_cardinality. Unequal marker prefixes and unknown final
   spill cardinalities prevent deriving equal live-stack lengths or excluding
   opposite decisions. This accounting establishes no branch exclusion.

   Successor transport is separate: dfs_block_state_owner_alloc_origin gives
   successor D's map equal to SOME owner's output A, same free list/base and
   monotone highwater. unique_predecessor_owner_origin identifies its LABEL,
   not its input/run with AD. Use of the desired inclusion above also needs
   comparison of AD's occupied addresses with actual owner's A (e.g. input
   uniqueness plus determinism). Only then can occupied-address transport
   splice AL into D. Existing join empty-spill transport avoids this issue.
   Do not conflate the owner comparison with the two same-code lineage runs.
*)
