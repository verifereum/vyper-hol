Theory fnPlanLineageStageAudit
Ancestors
  fnPlanLineageInventory fnPlanLineageReplay fnPlanLineageSuffix planWf
  stackPlanGen stackPlanOps stackModel venomInst

(* These are local stage-interface tests, not reachable-ready-program claims. *)
Theorem offset_retains_output:
  (SND (generate_offset_plan
    (mk_inst 0 OFFSET [Lit 0w; Label "L"] ["x"])
    (init_plan_state 0))).ps_stack = [Var "x"]
Proof
  EVAL_TAC >> simp[]
QED

Theorem regular_dead_output_stages:
  (SND (generate_regular_inst_plan ARB dfg_empty ARB ARB
    (mk_inst 0 ISZERO [Lit 0w] ["x"]) [] F F "entry"
    (init_plan_state 0))).ps_stack = [] /\
  (SND (generate_regular_inst_plan ARB dfg_empty ARB ARB
    (mk_inst 0 ISZERO [Lit 0w] ["x"]) [] T F "entry"
    (init_plan_state 0))).ps_stack = [Var "x"]
Proof
  EVAL_TAC >> simp[]
QED

Theorem repeated_input_stages:
  (SND (emit_input_plan ADD [Var "a"; Var "a"] []
    ((init_plan_state 0) with ps_stack := [Var "a"])) ).ps_stack =
      [Var "a"; Var "a"] /\
  (SND (generate_regular_inst_plan ARB dfg_empty ARB ARB
    (mk_inst 0 ADD [Var "a"; Var "a"] ["x"]) [] F F "entry"
    ((init_plan_state 0) with ps_stack := [Var "a"])) ).ps_stack = []
Proof
  EVAL_TAC >> simp[]
QED

Theorem phi_dead_output_stages:
  (SND (generate_phi_plan (mk_inst 0 PHI [Var "a"; Var "b"] ["x"])
    [] F ((init_plan_state 0) with ps_stack := [Var "a"])) ).ps_stack = [] /\
  (SND (generate_phi_plan (mk_inst 0 PHI [Var "a"; Var "b"] ["x"])
    [] T ((init_plan_state 0) with ps_stack := [Var "a"])) ).ps_stack = [Var "x"]
Proof
  EVAL_TAC >> simp[]
QED

Definition stage_param_fn_def:
  stage_param_fn = mk_raw_function "entry"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 0 PARAM [Lit 0w] ["dead"];
       mk_inst 1 PARAM [Lit 1w] ["live"];
       mk_inst 2 RETURN [Var "live"; Lit 0w] []] |>]
End

Theorem param_dead_live_stage:
  (SND (prepare_params_plan (liveness_analyze stage_param_fn)
    stage_param_fn (init_plan_state 0))).ps_stack = [Var "live"]
Proof
  EVAL_TAC >> simp[]
QED

Theorem phi_present_rename_stage:
  generate_phi_plan (mk_inst 0 PHI [Var "a"; Var "b"] ["x"])
    ["x"] F ((init_plan_state 0) with ps_stack := [Var "a"]) =
  ([SOPoke 0 (Var "x")], (init_plan_state 0) with ps_stack := [Var "x"])
Proof
  irule EQ_TRANS >> irule_at Any generate_phi_plan_rename_only >>
  qexists_tac `0` >> EVAL_TAC
QED

(* Stage-contract audit (design output; the signatures below are proposals,
   NOT additional proved preservation theorems).

   Notation in this comment only:
     I(S,p) = lineage_inventory S p; V(xs) = set (MAP Var xs).
     S is the represented variable inventory, not a liveness set.
     L is next_liveness; R = S DIFF V(current_live) is residual inventory.
   Source boundaries: stackPlanGen generate_* definitions, stackPlanOps
   emit_input_plan/restore_spilled_plan/popmany_plan; livenessDefs
   liveness_transfer/input_vars_from; venomWf inst_wf/ssa_form/
   def_dominates_uses. Existing generic accounting lemmas live in Inventory;
   existing PHI rename interface is in Replay, reused above.

   Family       Stable accounting / transient obligation
   PARAM        generate_inst_plan is identity. prepare_params_plan first
                pushes all parameter outputs, then removes variable slots
                not in live_vars_at entry (LENGTH params). From empty entry
                inventory the intended result is V(live parameter outputs).
                Nonempty arbitrary inputs require accounting for their removal
                too: to_pop scans the entire stack, not just new parameters.
   PHI          Selects one PRESENT incoming alternative, not necessarily the
                syntactically first one. Rename removes that identity and adds
                the output; if incoming remains live it duplicates instead.
                Dead output removed only when nonhalting. NONE depth is a
                no-op, not an error. Needs predecessor-indexed coverage and
                uniqueness of the represented alternative before selection.
   OFFSET       Well-shaped OFFSET pushes its fresh output unconditionally:
                S' = S UNION {Var out}; spills unchanged. This is true even
                if out is dead. No liveness-based output pop or spill release.
   NOP          Dispatch identity, including spilled inventory. A liveness
                specialization must separately establish the transfer identity.
   Ordinary     emit_input_plan can duplicate live inputs and repeated inputs,
                and push literals. Reorder/pop must consume exactly the
                operand occurrences before distinct variable inventory resumes.
                Retained old identities plus live fresh outputs remain; dead
                spills are released. Old dead residual STACK identities are
                not swept. Successful planning alone does not give coverage.
   JMP          No ordinary input operands. Restore spilled target variables,
                reorder target suffix, release dead spills. join_reached checks
                suffix equality only. Neither it nor restore/reorder deletes
                old residual stack identities below that suffix.
   Halting      bb_is_halting is passed to EVERY instruction in the block.
                PHI and ordinary single-output stages can retain dead outputs;
                ordinary multi-output stages still pop dead outputs. There is
                no outgoing execution edge requiring canonical live-out, but
                preceding instructions in that block still need replay.

   Candidate local transfer signatures (schematic premise bundles must be
   decomposed/validated before formalizing; these are not new assumptions in
   the frozen theorem):
   * OFFSET: I(S,p) /\ inst_wf i /\ i.opcode=OFFSET /\
       Var(HD i.outputs) NOTIN S ==> I(S UNION {Var(HD i.outputs)}, SND result).
   * PARAM dispatch / NOP: I(S,p) ==> I(S,SND result).
   * Entry parameters: empty initial stack/spills, canonical parameter prefix,
       distinct fresh parameter outputs, and analyzed entry coverage ==>
       I(V(FILTER live parameter_outputs), SND prepare_params_plan result).
   * PHI rename-only: I(S,p), exactly one selected incoming a in stack core,
       a not live after prefix, fresh output x, adequate physical depth ==>
       I((S DELETE Var a) UNION kept_output, SND result), where kept_output
       is {Var x} for live x or halting, otherwise EMPTY. The duplicate branch
       keeps a and requires its own transient/depth proof. Incoming-in-spills
       cannot be handled by this signature: generate_phi_plan does not restore.
   * Ordinary: I(S,p), covered input occurrences, fresh distinct outputs,
       exact physical preparation/reorder/pop contract ==>
       I((S DIFF consumed_old_variables DIFF released_spills) UNION
         kept_outputs, SND result). consumed_old_variables must be derived
       from emit_input_plan's duplication decisions, not set(inst.operands).
   * JMP: I(S,p), target coverage and successful generate_inst_plan ==>
       inventory after restoring/releasing plus target suffix. Canonical join
       needs the EXTRA result S_after = set target_ops; only THEN can existing
       inventory/suffix boundaries exclude residual core and residual spills.

   Premise sources and gaps:
   - inst_wf OFFSET requires [Lit v; Label lbl] and one output (venomWf);
     it does not require that output to have a use. single_use_form counts
     uses at most once across nonexempt instructions, not at least once.
     Thus neither rules out the dead OFFSET probe.
   - ssa_form gives ALL_DISTINCT flattened instruction outputs. This supplies
     syntactic output uniqueness, NOT freshness against a state reached by
     revisiting a defining block: a separate provenance/loop argument is needed.
     def_dominates_uses gives definition availability, not represented-stack
     coverage; it cannot justify skipping the inventory preservation proof.
   - live_vars_at_transfer and live_vars_at_uses (livenessAnalysisProps) require
     wf_function, DFS-pre membership, lookup, and instruction index bounds.
     They relate analyzed lists via live_update(defs,uses), not physical stacks.
   - analyzed_live_out_edge_subset / singleton / jmp (LineageLiveness) require
     predecessor cfg_reachable_of plus block lookups; JMP gives equality with
     input_vars_from, not equality of physical inventory with those inputs.
   - phi_operands_ready excludes cross-PHI sharing and incoming names live
     after the PHI prefix; phi_edge_uses_wf supplies the named edge alternative.
     Deriving physical presence/absence of other alternatives remains open.

   Cleanup/join consumer audit:
   clean_stack_plan is active only for a singleton predecessor with several
   successors. Its deletion candidates are predecessor analyzed live-out minus
   successor inputs, so residual identities outside that analyzed layout are
   NOT candidates. The NULL-input safe branch marks the whole stack dead;
   other safe branches mark only retained candidates. All no-op branches
   preserve residual identities. In particular, JMP predecessors (one successor)
   get no successor cleanup, and restore/reorder plus join_reached cannot remove
   an extra dead OFFSET slot. Exact-liveness inventory at such an edge is not
   established by any of these boundaries. This is an interface gap, not a
   checked counterexample to lineage_state_block_plan: reachable ready function
   construction and its two path states have not been certified here.

   Checkpoint recommendation: select a residual-aware replay interface or
   investigate a reachable residual-join counterexample before attempting
   global exact-liveness preservation. No global invariant is defined here.
*)

(* Residual observation threshold probe: DUP's first deep branch is dist=16.
   The queried a is inside the common core on both sides, not in prefix r.
   Both sides have enough items for every bulk-spilled top chunk. *)
Theorem excluded_prefix_dup_threshold:
  !n. MEM n [15; 16] ==>
    FST (do_dup n ((init_plan_state 0) with
      ps_stack := [Var "r"; Var "a"] ++ REPLICATE n (Lit 0w))) =
    FST (do_dup n ((init_plan_state 0) with
      ps_stack := [Var "a"] ++ REPLICATE n (Lit 0w))) /\
    (SND (do_dup n ((init_plan_state 0) with
      ps_stack := [Var "r"; Var "a"] ++ REPLICATE n (Lit 0w)))).ps_alloc =
    (SND (do_dup n ((init_plan_state 0) with
      ps_stack := [Var "a"] ++ REPLICATE n (Lit 0w)))).ps_alloc
Proof
  simp[] >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

(* Residual consumer audit, following excluded-prefix depth boundary.
   Source locations below refer to definition names (stable across insertions).
   This table records proposed contracts, NOT proved global closure.

   Consumer / queries / physical observations / code-relevant fields
   ----------------------------------------------------------------------
   stackModel.stack_get_depth: query op. bottom_excluded handles absent-prefix
     op even if absent from core. stack_get_phi_depth instead queries EVERY
     alternative in phis; stack_find_append_excluded is its direct interface.
   stack_get_unfixed_depth: query op outside protected depths (f,n). If n>f+1
     it enumerates LENGTH stack, so ordinary depth equality alone is not a
     ready-made rewrite. Need exclusion of op in prefix and indexed peek
     extension for d<LENGTH core; later enumerated prefix cannot match op.
   emit_one_input/emit_input_plan: queries variable inputs, also repeats in
     operand_vars rest; next_live decides duplication. Same ps_spilled and
     ps_alloc give identical restore offsets and frees. Literals/labels push
     no depth query. Duplicating existing depth d requires d<LENGTH core.
   do_dup: shallow d<=15; deep k=d-15 uses top_n k, allocator/free slots and
     a secondary k<=16 branch. Same d means same branch, even across 15/16.
     Require k<=LENGTH core (implied by valid d<LENGTH core). Prefix must not
     enter top_n k. excluded_prefix_dup_threshold checks operation/allocator
     equality at 15 and 16; both compared states satisfy this core bound.
   do_swap: shallow d<=16; deep chunk=d+1 uses top_n chunk and total-length
     subtraction to retain base. Require d<LENGTH core; then chunk<=LENGTH
     core, base retains prefix and spill count is unchanged. Existing
     stack_swap_bottom_extension only proves the shallow physical update;
     deep code/allocator equality still needs its own boundary.
   select_spill_candidate: inspects variable identities at offsets up to
     MIN 16 (MIN (target_dist-1) (LENGTH stack-1)), excluding forbidden targets
     and offsets <target_len. Require target_dist<LENGTH core. Then the MIN
     length bound cannot expose prefix, and all candidate peeks are in core.
   reduce_depth_plan: acts only for queried dist>16; called with fuel=LENGTH
     stack, so related states have different fuel! Need adequate-fuel result
     (or a bounded count of successful spills before shallow/no-candidate
     exit), not equal-fuel induction. Each spill must remain inside core and
     preserve target coverage; prefix variables are NOT interchangeable with
     markers if the candidate window can reach them. This boundary is open.
   reorder_one/reorder_plan: queries targets and at_target via operand_equiv
     dfg. final_dist = LENGTH targets-1-idx must be <LENGTH current core at
     each effective move, including before the explicit total-length guard.
     Need unfixed coverage outside the protected window, not mere set coverage
     when targets repeat. Requires same dfg, spilled map and allocator.
     Commutative dry runs compare reorder_cost, hence need equality of both
     candidate operation lists before reusing the selected result.
   popmany_plan: queries deletion operands and sorts by depth. Contiguous
     fast path n<=16 swaps depth n, requiring n<LENGTH core; depths 1..n
     imply this only with genuine common-core occurrence bounds. Individual
     path needs each current deletion depth<LENGTH current core. No deletion
     may consume a prefix identity. Generic Inventory deletion lemmas have
     their own distinct-core assumptions; not valid for transient duplicates.
   optimistic_swap_plan: queries Var(LAST next_liveness), compares output via
     operand_equiv dfg; then do_swap with its core depth bound. It does not
     iterate through all physical residual variables.
   release_dead_spills: does not inspect stack length. Identical spilled maps,
     allocators and next_live suffice; otherwise frees can distinguish paths.
   generate_phi_plan: queries ALL variable alternatives, peeks selected depth,
     then dup/poke and optional dead-output pop. Needs exclusion of every
     alternative from residual prefix, selected alternative in core, and fresh
     output identity absent from prefix for any later output-pop query.
   generate_regular_inst_plan: composes above with join_target_ops and emitter.
     Popping LENGTH operands requires that many actual prepared core slots.
     Fresh output pushes preserve prefix but do not remove residual identities.
     generate_emit_ops may change label counter (INVOKE/ASSERT_UNREACHABLE),
     so equal ps_label_counter is required, not only same stacks and spills.
   generate_inst_plan: dispatch itself uses instruction shape, not total stack
     length. JMP guard join_reached also needs LENGTH targets<=LENGTH core
     and common target suffix to strip prefix in its pop equation. OFFSET
     creates a new residual output if dead; PARAM/NOP are identity dispatches.
   clean_stack_plan: queries analyzed layout-minus-input variables and inputs
     via below_all_live; tests physical stack length in cleanup_height_safe
     and writes ps_cleanup_promised. Its safe/unsafe branch must be coordinated
     via allowed height/promise overrides, not assumed invariant under prefix.
     For non-NULL inputs, prefix excluded from candidate names survives; for
     NULL inputs and safe elision, the ENTIRE prefix becomes markers. No-op
     branches preserve it. Generic exact-inventory cleanup lemmas cannot
     assume an uncounted residual prefix away.

   Candidate invariant, with producer status kept separate:
   (A) stacks prefix1++core and prefix2++core, same spill map, allocator,
       label counter, growth and other code-relevant fields; cleanup height
       and promise may differ. Same spill/alloc fields are a PROOF OBLIGATION,
       not a consequence of operation equality, especially after branch paths.
   (B) query exclusion includes current operands, selected-edge PHI alternatives,
       target input_vars_from, output names used by postprocessing, and cleanup
       candidates. These sets change at every stage; exclusion must be produced
       by a temporal provenance/liveness argument, not globally postulated.
   (C) every effective move/dup/pop window stays within core, with unfixed
       multiplicity coverage and adequate reduction fuel. Deep bulk spills
       obey explicit inequalities listed above; cardinality of live names
       does not prove physical location or multiplicity.
   (D) branch and join boundaries must establish common core layout while
       allowing different prefixes. OFFSET may leave its new dead output on
       TOP temporarily, so a bottom-prefix invariant is not closed immediately
       at OFFSET: relocation into the residual region needs a stage argument.

   Known premise producers vs missing work:
   analyzed_live_out_jmp and analyzed_live_out_edge_subset give analyzed target
   relationships on reachable edges only. live_vars_at_transfer/uses/propagate
   give ordinary pointwise liveness on reachable block indexes. These theorems
   do not give A, C, or D. ssa_form prohibits two syntactic defining instructions
   for the same name; def_available_at supplies dominance/order for uses, and
   phi_operands_ready separates PHI alternatives after the prefix. No imported
   theorem yet proves B for all dynamic residual states. In a cycle the SAME
   defining instruction can execute again: SSA alone does not make its output
   fresh against its earlier residual instance. A later loop redefinition may
   cause output-pop or PHI search to observe that instance. Need temporal
   deadness/provenance or a stronger identity-erasure boundary; do not assert
   that analyzed deadness implies a name is never queried on a later traversal.

   Result: depth observations admit the new excluded-prefix boundary and the
   first DUP threshold test is positive. Remaining precise obstructions are
   adequate-fuel reduction, common-core location through OFFSET, dynamic
   name exclusion across cycles, and reachable spill/allocator alignment.
   Return these contracts to the strategist; no global equivalence or
   preservation theorem has been added by this audit.
*)

(* Consumer-minimal physical test: with a nonempty lower prefix, the
   core-height bound is necessary as well as sufficient for pop framing.
   The undersized case includes windows fitting the whole stack but
   intersecting its marker prefix; no resource-count premise repairs it. *)
Theorem stack_pop_nonempty_prefix_frame_iff:
  !prefix core n.
    prefix <> [] ==>
    (stack_pop n (prefix ++ core) = prefix ++ stack_pop n core <=>
     n <= LENGTH core)
Proof
  rpt gen_tac >> strip_tac >> eq_tac
  >- (disch_then (mp_tac o AP_TERM ``LENGTH : 'a list -> num``) >>
      simp[stackModelTheory.stack_pop_def, listTheory.LENGTH_TAKE] >>
      `0 < LENGTH prefix` by (Cases_on `prefix` >> gvs[]) >> decide_tac) >>
  strip_tac >> simp[stackModelTheory.stack_pop_def, rich_listTheory.TAKE_APPEND,
    listTheory.TAKE_LENGTH_TOO_LONG]
QED

(* A target suffix is not an empty-pending certificate. This symbolic
   obstruction allows arbitrary prefix, allocator, spills and demand list. *)
Theorem repeated_suffix_excludes_empty_budget:
  !base ps prefix targets op.
    1 < LIST_ELEM_COUNT op targets /\ ps.ps_stack = prefix ++ targets ==>
    ~residual_budget_wf base [] ps
Proof
  rpt gen_tac >> strip_tac >>
  disch_tac >>
  qpat_x_assum `residual_budget_wf _ _ _`
    (strip_assume_tac o REWRITE_RULE [reorderSimTheory.residual_budget_wf_def]) >>
  qpat_x_assum `!x. LIST_ELEM_COUNT x _ <= SUC _`
    (qspec_then `op` mp_tac) >>
  simp[reorderSimTheory.elem_count_append, rich_listTheory.LIST_ELEM_COUNT_THM] >>
  decide_tac
QED

(* C3.resources.producers.interface -- consumer-directed resource ledger.
   This updates the earlier ledger above: several earlier open LOCAL frame
   facts now exist in Inventory. It does not certify reachable producers.

   Exact resource predicate (reorderSim.residual_budget_wf_def):
     residual_budget_wf b pending p <=>
       plan_slots_bounded b p /\
       spill_alloc_layout_wf p.ps_alloc p.ps_spilled /\
       (!x. LIST_ELEM_COUNT x p.ps_stack <= SUC (LIST_ELEM_COUNT x pending)) /\
       (!x. x IN FDOM p.ps_spilled ==>
            LIST_ELEM_COUNT x p.ps_stack <= LIST_ELEM_COUNT x pending).
   These are FOUR independent requirements: slot bound, allocator layout,
   multiplicity upper bound, and stack/spill overlap bound. There is no
   physical lower bound in this predicate. In the table p[core] abbreviates
   p with ps_stack := core (comment notation only).

   Consumer family                 pending / actual use / existing boundary
   ---------------------------------------------------------------------
   Input emission resource         pending -> pending++operands. Inventory
     emit_input_plan_marker_core_budget uses residual_budget_wf for count and
     layout preservation. Coverage is a SEPARATE premise. It is not needed
     by emit_input_plan_bottom_frame, which needs target exclusion from the
     prefix and agrees exactly on all non-stack fields via the record frame.
   Ordinary preparation            [] -> operands or PERM-selected operands.
     emit_reorder_plan_marker_core_reserve and
     emit_reorder_pop_marker_execution start with [] on p[core].
     available_input_plan_length supplies the physical post-emission floor
     from coverage, not residual_budget_wf. Reorder's protected consumption
     additionally uses counts to reserve live values below consumed operands.
   Reorder resource                 pending -> SAME pending.
     reorder_plan_marker_core_inventory/reserve require the SEPARATE bounds
     LENGTH pending<=LENGTH core and LENGTH pending<=16. Reserve additionally
     requires count(pending,v)+live(v)<=count(core,v)+spilled(v).
     For CODE framing only, reorder_plan_bottom_frame has the exact signature:
       EVERY (\op. ~MEM op prefix) targets /\
       LENGTH targets <= LENGTH p.ps_stack /\
       reorder_plan dfg targets p = (ops,q) ==>
       reorder_plan dfg targets (p with ps_stack := prefix++p.ps_stack) =
         (ops,q with ps_stack := prefix++q.ps_stack).
     No budget, target distinctness, or <=16 premise is needed here. Its
     reduce_depth_plan_height_bottom_frame already handles unequal height
     fuels; the earlier ledger's LOCAL fuel obstruction is now resolved.
   Consumption cancellation        pending -> []. Exact existing signature:
       p.ps_stack=rest++pending /\ residual_budget_wf b pending p ==>
       residual_budget_wf b [] (p with ps_stack:=rest)
     (Inventory.residual_budget_wf_suffix_cancel). This is a CONSUMED suffix,
     not a license to replace pending by [] while leaving pending on stack.
   Fresh output push               [] -> []. Setup.fresh_outputs_residual_budget
     and output_push_marker_core require distinct outputs absent from both
     stack and spills; counts and overlap matter, not just physical height.
   Opcode emission                 arbitrary pending -> SAME pending.
     Setup.generate_emit_ops_residual_budget_wf/core_resource use unchanged
     slots and allocator; no count transformation. Code pairing additionally
     needs equal label counters (native emitter can generate fresh labels).
   Dead output pop / optimistic    [] -> []. Setup.popmany_plan_core_resource,
     optimistic_swap_plan_core_resource and regular_post_emit_tail_core_resource
     use distinct core and spill-disjointness from empty budget. Physical
     versions popmany_plan_prefix_replay and do_swap_prefix_replay instead
     require actual lookup/window confinement. No empty-pending PHI/JMP
     certificate is established by these conditional ordinary boundaries.
   Spill release                   arbitrary pending -> SAME pending.
     Setup.residual_budget_wf_release_dead_spills/core preserve counts and
     layout by deleting spill bindings and freeing matching offsets. Pairing
     requires identical spill maps AND allocator, not stack suffix alone.
   Whole ordinary stage            [] -> []. Setup.native_regular_core_resource
     needs opcode<>JMP, operand length<=16, coverage, marker exclusion,
     output freshness/distinctness. Callers.ordinary_position_invariant also
     needs definition support to produce freshness and next-position support.
   Cleanup                         NO residual_budget_wf premise.
     Inventory.clean_stack_plan_prefix_replay needs common variable core,
     ALL_DISTINCT core, equal allocators, and (in its active branch) core
     subset of successor inputs UNION predecessor live-out. Existential
     promise with height NONE coordinates the elision branch. It permits NEW
     marker counts m',n'. Neither counts nor common core are produced by the
     theorem. NULL inputs may mark the whole stack, not a fixed prefix.
   PHI schedule                    NO residual_budget_wf premise.
     PhiTemporal.phi_origin_schedule_state_replay needs
       phi_origin_schedule_ready steps p q cells cells_end,
       left.stack=p++MAP(phi_cell_value T)cells,
       right.stack=q++MAP(phi_cell_value F)cells, left.alloc=right.alloc.
     It returns equal ops and allocator and framed final cell projections.
     It preserves the other state fields individually; equal spills must
     therefore be supplied at entry. Origin extinction is not count<=1 for
     every unmapped repeated base operand in the final cells.

   Proposed separated stage interfaces (NOT claimed as produced invariants):
   Ordinary paired entry: stacks REPLICATE m marker++core and
     REPLICATE n marker++core; equal spills/allocator/label-counter; separate
     slot/layout facts; current query coverage/exclusion and confined windows.
     To reuse existing ordinary RESOURCE producers, also require [] budget on
     each core state, live lower coverage and definition-supported freshness.
     The code-frame part is weaker than this resource-preservation interface.
   Post-JMP paired entry: stacks REPLICATE m marker++coreP and
     REPLICATE n marker++coreQ with corresponding target/cell suffixes;
     equal allocators, empty spills and equal label counter; separate slot/
     layout facts. Keep the ACTUAL pending targets in any count certificate.
     Allow new m,n. No [] budget on full coreP/coreQ is inferred. JoinEntry's
     successful_join_edges_native_cells supplies cell projections/classes,
     but NOT a marked-prefix decomposition or allocator equality.
   Post-PHI paired entry: same non-stack equalities, projected final cells
     become a common suffix after origin extinction. Require residual-prefix
     query exclusion and physical windows separately. To call the existing
     first ordinary resource theorem, a further []-budget common-core result
     is needed; it does not follow merely by completing the PHI schedule.

   Symbolic acceptance/rejection tests, arbitrary lists (no fold EVAL):
   - stack_pop_nonempty_prefix_frame_iff above gives the EXACT minimum bound
     n<=LENGTH core. If LENGTH core<n, framing fails, even when
     n<=LENGTH prefix+LENGTH core. Thus a target window intersecting markers
     cannot be justified by its fitting the whole stack. This tests both
     undersized branches of the proposed physical interface at consumption.
   - repeated_suffix_excludes_empty_budget above rejects [] budget whenever
     any retained target has multiplicity>1, for ANY prefix/spills/allocator.
     This is an interface obstruction, not a reachable counterexample.
   - residual_budget_wf_suffix_cancel is the already checked positive test:
     cancellation succeeds only after physically removing the pending suffix.
     JMP does not remove its target suffix. PHI edits are not that pop.

   Missing producers, stated at their use boundary:
   (1) Actual paired JMP exits must produce common allocator/label fields,
       empty spills and corresponding cell suffixes with residual-prefix
       exclusion; pre-reorder core floor remains a separate question.
   (2) Actual PHI exits must either produce a common []-budget core for the
       existing ordinary producers, or ordinary producers must be generalized
       to a reviewed allowance for retained repeated base values. Suffix plus
       empty spills alone does NOT supply the existing consumer premises.
   (3) Cleanup's common distinct variable core and active subset premise need
       a producer, with coordinated override choices and new marker counts.
   No new certificate definition is introduced: the candidate post-PHI-to-
   ordinary bridge fails the sufficiency audit without (2). In particular,
   this audit is not proof that native successful states violate that bridge;
   global success could exclude the offending multiplicities, but no theorem
   establishing such exclusion is available. Frozen theorem is untouched.
*)

(* PHI lower-prefix audit: selection locality is already exported as
   stack_get_phi_depth_suffix_hit in fnPlanLineageSuffix. No exclusion
   premise is needed when the suffix search succeeds. *)
Theorem stack_get_phi_depth_bound:
  stack_get_phi_depth alternatives core = SOME d ==> d < LENGTH core
Proof
  simp[stack_get_phi_depth_def] >> strip_tac >>
  drule stack_find_bound >> simp[]
QED

Theorem phi_colliding_prefix_selection:
  stack_get_phi_depth [Var "a"] [Var "a"] = SOME 0 /\
  stack_get_phi_depth [Var "a"] [Var "a"; Var "z"; Var "a"] = SOME 0
Proof
  EVAL_TAC
QED

Theorem phi_colliding_prefix_rename:
  (generate_phi_plan (mk_inst 0 PHI [Var "a"] ["r"]) ["r"] F
    ((init_plan_state 0) with ps_stack := [Var "a"; Var "z"; Var "a"])) =
  ([SOPoke 0 (Var "r")],
    (init_plan_state 0) with ps_stack := [Var "a"; Var "z"; Var "r"])
Proof
  EVAL_TAC
QED

Theorem phi_colliding_prefix_duplicate:
  (generate_phi_plan (mk_inst 0 PHI [Var "a"] ["r"]) ["a"; "r"] F
    ((init_plan_state 0) with ps_stack := [Var "a"; Var "z"; Var "a"])) =
  ([SODup 1; SOPoke 0 (Var "r")],
    (init_plan_state 0) with ps_stack := [Var "a"; Var "z"; Var "a"; Var "r"])
Proof
  EVAL_TAC
QED

Theorem phi_colliding_prefix_dead_output:
  (generate_phi_plan (mk_inst 0 PHI [Var "a"] ["r"]) [] F
    ((init_plan_state 0) with ps_stack := [Var "r"; Var "a"])) =
  ([SOPoke 0 (Var "r"); SOPop 1],
    (init_plan_state 0) with ps_stack := [Var "r"])
Proof
  EVAL_TAC
QED

(* Physical PHI consumer contract (not a reachable-state invariant):
   - Incoming selection: stack_get_phi_depth_suffix_hit and the bound above
     allow arbitrary lower prefixes, even colliding incoming names. A suffix
     hit must still be produced for EACH stage; entry coverage alone does
     not establish preservation after previous writes/pops.
   - Selected-live test: with d inside the suffix, stack_peek is suffix-local;
     paired executions need agreement of the selected values' live tests,
     not absence of incoming values in their prefixes (phi_origin_selected).
   - Rename: stack_poke at the selected in-suffix depth preserves the prefix.
     No prefix exclusion is needed. The duplicate branch additionally needs
     the do_dup physical window and paired allocator equality for deep d;
     locality of the initial search is not an allocator replay theorem.
   - Dead output: the write creates ret in the suffix, so its first search
     cannot be displaced by a lower-prefix ret, as the checked example shows.
     popmany_plan [ret] still needs a bounded do_swap/pop window. Its singleton
     contiguous case has depth 1 and swaps 1, hence requires two suffix cells;
     depth 0 uses the individual path. General multi-item popmany bounds must
     not be inferred from this singleton PHI observation.
   - optimistic_swap_plan is NOT called by generate_phi_plan. Subsequent block
     cleanup/reordering has separate physical windows and query obligations.
   Therefore blanket exclusion of incoming/output names from residual prefixes
   is overstrong for a covered PHI selection/write. The next useful producer
   is suffix hit/selected-live preservation through the native schedule, with
   explicit bounded dead-output and deep-dup effects, NOT global exclusion.
   None of these local tests is a counterexample to lineage_state_block_plan. *)

(* Lower-reserve probes deliberately allow repeats and stack/spill overlap.
   These are local computations, not claims of reachable planner states. *)
Theorem repeated_protected_consumption_probe:
  MEM (Var "a")
    (stack_pop 2
      (SND (reorder_plan dfg_empty [Var "a"; Var "a"]
        (SND (emit_input_plan ADD [Var "a"; Var "a"] ["a"]
          ((init_plan_state 0) with ps_stack :=
            [Var "a"; Var "a"; Var "a"])) ))).ps_stack)
Proof
  EVAL_TAC
QED

Theorem overlap_protected_consumption_probe:
  MEM (Var "b")
    (stack_pop 1
      (SND (reorder_plan dfg_empty [Var "a"]
        (SND (emit_input_plan ISZERO [Var "a"] ["b"]
          ((init_plan_state 0) with <|
            ps_stack := [Var "b"; Var "b"; Var "a"];
            ps_spilled := FEMPTY |+ (Var "b", 0) |>)) ))).ps_stack)
Proof
  EVAL_TAC
QED

Definition lower_reserve_deep_state_def:
  lower_reserve_deep_state = (init_plan_state 0) with <|
    ps_stack := [Var "a"] ++ REPLICATE 17 (Var "b");
    ps_spilled := FEMPTY |+ (Var "b", 0) |>
End

Theorem deep_overlap_protected_consumption_probe:
  Var "b" IN FDOM
    (SND (reorder_plan dfg_empty [Var "a"]
      (SND (emit_input_plan ISZERO [Var "a"] ["b"]
        lower_reserve_deep_state)))).ps_spilled /\
  MEM (SOSpill 0)
    (FST (reorder_plan dfg_empty [Var "a"]
      (SND (emit_input_plan ISZERO [Var "a"] ["b"]
        lower_reserve_deep_state))))
Proof
  EVAL_TAC
QED

Theorem deep_overlap_inventory_drop_probe:
  LIST_ELEM_COUNT (Var "b") lower_reserve_deep_state.ps_stack +
    (if Var "b" IN FDOM lower_reserve_deep_state.ps_spilled then 1 else 0) = 18 /\
  LIST_ELEM_COUNT (Var "b")
    (SND (reorder_plan dfg_empty [Var "a"]
      lower_reserve_deep_state)).ps_stack = 16 /\
  stack_peek 0 (SND (reorder_plan dfg_empty [Var "a"]
    lower_reserve_deep_state)).ps_stack = Var "a"
Proof
  EVAL_TAC
QED

(* Lower-reserve audit, after the checked probes above:
   emit_reorder_plan_core_protected_consumption currently calls
   emit_reorder_plan_core_suffix (which uses residual_budget_wf both for
   materialised_suffix and its propagated budget), then calls
   reorder_plan_inventory_mono. Removing the budget premise from that
   inventory theorem is invalid: deep_overlap_inventory_drop_probe loses
   one unit of count-plus-domain inventory while keeping b available.

   For bounded materialised inputs, reorder_one_materialised_counts_unconditional
   already preserves ALL counts of target operands provided its unfixed hit
   exists. The materialised_fold_bottom_frame proof obtains each next hit
   using the fixed-window and target-count interfaces without a budget.
   This suggests reusing that induction for a budget-free suffix theorem;
   suffix correctness is still required, not supplied by these tests.

   For a protected variable NOT in targets, reduction only spills variables
   excluded from targets; do_spill_at removes one stack occurrence and adds
   a spill binding (possibly overwriting one). Thus positive count-plus-spill
   is preserved, though its full value is not. For a target variable,
   materialised counts are preserved, but consumption needs its EXTRA live
   reserve too. Exact target stack count preservation supplies this when
   the reserve is a stack occurrence; a reserve in the spill domain needs
   a separate preservation fact (restore cannot run when an unfixed stack
   hit was obtained). Placement swaps or the operand_equiv two-poke branch
   permute physical values and do not discard a protected non-target.

   Smallest proposed universal boundary for review: under materialised
   counts, length floor and fixed suffix at stage idx, one reorder_one step
   preserves (a) fixed suffix extended by op, (b) target stack counts,
   (c) each protected Var v's count-plus-spill lower bound capped at
   count(targets,Var v)+1. Use separate non-target positive-availability
   and target-spill-preservation lemmas instead of uncapped inventory mono.
   No global reachability or suffix-local availability follows from these
   local computations. Optimistic code shielding remains separate. *)
