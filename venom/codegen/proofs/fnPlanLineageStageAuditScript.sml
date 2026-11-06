Theory fnPlanLineageStageAudit
Ancestors
  fnPlanLineageInventory fnPlanLineageReplay fnPlanLineageSuffix planWf
  fnPlanLineageEntryProbe
  stackPlanGen stackPlanOps stackModel venomInst list rich_list
Libs wordsLib

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

(* Local producer probe: the prefix is not claimed reachable. *)
Definition optimistic_producer_core_def:
  optimistic_producer_core = [Var "a"] ++ REPLICATE 16 (Lit 0w) ++ [Var "b"; Lit 0w]
End

Definition optimistic_producer_reordered_def:
  optimistic_producer_reordered prefix =
    SND (reorder_plan dfg_empty [Var "a"]
      (SND (emit_input_plan ISZERO [Var "a"] ["out"; "b"]
        ((init_plan_state 0) with ps_stack := prefix ++ optimistic_producer_core))))
End

Theorem optimistic_producer_spills_query_probe:
  Var "b" IN FDOM (optimistic_producer_reordered []).ps_spilled /\
  ~MEM (Var "b") (optimistic_producer_reordered []).ps_stack /\
  MEM (Var "b") (optimistic_producer_reordered [Var "b"]).ps_stack
Proof
  EVAL_TAC
QED

Definition optimistic_producer_pre_swap_def:
  optimistic_producer_pre_swap prefix =
    (optimistic_producer_reordered prefix) with ps_stack :=
      stack_pop 1 (optimistic_producer_reordered prefix).ps_stack ++ [Var "out"]
End

Theorem optimistic_producer_enabled_query_probe:
  (mk_inst 0 ISZERO [Var "a"] ["out"]).inst_outputs <> [] /\
  FILTER (\v. MEM v ["out"; "b"]) ["out"] <> [] /\
  ~operand_equiv dfg_empty (Var "out") (Var "b") /\
  stack_get_depth (Var "b") (optimistic_producer_pre_swap []).ps_stack = NONE /\
  stack_get_depth (Var "b") (optimistic_producer_pre_swap [Var "b"]).ps_stack <> NONE /\
  FST (optimistic_swap_plan dfg_empty (mk_inst 0 ISZERO [Var "a"] ["out"])
    ["out"; "b"] F (optimistic_producer_pre_swap [])) = [] /\
  FST (optimistic_swap_plan dfg_empty (mk_inst 0 ISZERO [Var "a"] ["out"])
    ["out"; "b"] F (optimistic_producer_pre_swap [Var "b"])) <> []
Proof
  EVAL_TAC
QED

Theorem optimistic_producer_native_ops_probe:
  FST (generate_regular_inst_plan lv dfg_empty cfg fn
    (mk_inst 0 ISZERO [Var "a"] ["out"]) ["out"; "b"] F F "block"
    ((init_plan_state 0) with ps_stack := optimistic_producer_core)) <>
  FST (generate_regular_inst_plan lv dfg_empty cfg fn
    (mk_inst 0 ISZERO [Var "a"] ["out"]) ["out"; "b"] F F "block"
    ((init_plan_state 0) with ps_stack := [Var "b"] ++ optimistic_producer_core))
Proof
  EVAL_TAC
QED

(* Optimistic producer ledger (E0253 follow-up):
   The new checked selective-spill fixture starts with a common core hit for
   the enabled query b, empty spills, and a hidden b in only one lower prefix.
   Input preparation/reorder spills the sole core b; the retained prefix b
   then becomes visible to optimistic_swap after operand consumption and the
   live output push. The full native ISZERO plans emit different operations.
   This is a local closure obstruction, NOT a reachable-program witness.

   Thus even initial suffix-local live coverage plus empty spills does not
   preserve query shielding through ordinary selective spilling. A sufficient
   stronger origin obligation is absence of all currently live names in the
   lower prefixes, together with suffix-or-spill availability. Selective spill
   cannot introduce a prefix occurrence, but preserving the chosen physical
   boundary and producing suffix coverage require their own stage theorems.
   LowerPrefix's exact-hit/swap frames remain the consumer interface; no new
   conditional optimistic frame is needed here.

   Initial-producer obligations not discharged by these probes:
   (1) Join/PHI residual prefixes may contain incoming bases (the checked PHI
       collision probes above explicitly allow this). Liveness transfer must
       show any base remaining in such a prefix is not queried live later,
       or a common suffix hit must survive for every relevant query stage.
   (2) PHI duplicate/rename/pop stages must establish the chosen suffix and
       prefix-exclusion property for actual subsequent live names, including
       names shared by repeated bases; global SSA alone is not a local proof.
   (3) Ordinary liveness transfer must propagate exclusion to the next live
       set, with fresh outputs created in the suffix and actual pop/spill
       windows preserving the boundary. Native live availability (Setup) is
       budget-free now, but supplies neither exclusion nor suffix-locality.
   No reachability, long-JMP coverage, or frozen-task falsehood is asserted. *)

(* Reachable join-origin diagnostics reuse EntryProbe's ready diamond and
   exact block-step observers. Two fixtures, with and without a PHI. *)
Definition prefix_audit_phi_fn_def:
  prefix_audit_phi_fn = residual_diamond_fn with fn_blocks :=
    LUPDATE ((EL 1 residual_diamond_fn.fn_blocks) with bb_instructions :=
      [mk_inst 10 ADD [Var "t"; Var "t"] ["unused"];
       mk_inst 1 ADD [Lit 10w; Lit 1w] ["a"];
       mk_inst 2 JMP [Label "J"] []]) 1 residual_diamond_fn.fn_blocks
End

Definition prefix_audit_plain_fn_def:
  prefix_audit_plain_fn = prefix_audit_phi_fn with fn_blocks :=
    LUPDATE ((EL 3 prefix_audit_phi_fn.fn_blocks) with bb_instructions :=
      [mk_inst 6 ADD [Var "t"; Lit 1w] ["y"];
       mk_inst 7 JMP [Label "exit"] []]) 3 prefix_audit_phi_fn.fn_blocks
End

Theorem prefix_audit_repeated_use_rejected:
  EVERY (\fn. ~codegen_ready_fn fn) [prefix_audit_phi_fn; prefix_audit_plain_fn]
Proof
  simpLib.SIMP_TAC bool_ss [listTheory.EVERY_DEF] >> conj_tac >> EVAL_TAC >> simp[]
QED

Theorem prefix_audit_success:
  EVERY (\fn. IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze fn) (dfg_build_function fn) (cfg_analyze fn)
    NONE [] fn 0 0)) [prefix_audit_phi_fn; prefix_audit_plain_fn]
Proof
  simpLib.SIMP_TAC bool_ss [listTheory.EVERY_DEF] >> conj_tac >>
  (computeLib.add_funs [listTheory.SET_TO_LIST_EMPTY]; EVAL_TAC)
QED

Theorem prefix_audit_incoming_stacks:
  (residual_incoming prefix_audit_plain_fn 1).ps_stack = [Var "t"] /\
  (residual_incoming prefix_audit_plain_fn 2).ps_stack = [Var "t"] /\
  (residual_incoming prefix_audit_phi_fn 1).ps_stack = [Var "t"; Var "a"] /\
  (residual_incoming prefix_audit_phi_fn 2).ps_stack = [Var "t"; Var "b"]
Proof
  rpt conj_tac >> EVAL_TAC
QED

Definition prefix_audit_exempt_fn_def:
  prefix_audit_exempt_fn = prefix_audit_phi_fn with fn_blocks :=
    LUPDATE ((EL 1 prefix_audit_phi_fn.fn_blocks) with bb_instructions :=
      [mk_inst 10 ASSIGN [Var "t"] ["unused"];
       mk_inst 1 ADD [Lit 10w; Lit 1w] ["a"];
       mk_inst 2 JMP [Label "J"] []]) 1 prefix_audit_phi_fn.fn_blocks
End

Theorem prefix_audit_exempt_ready_success:
  codegen_ready_fn prefix_audit_exempt_fn /\
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze prefix_audit_exempt_fn) (dfg_build_function prefix_audit_exempt_fn)
    (cfg_analyze prefix_audit_exempt_fn) NONE [] prefix_audit_exempt_fn 0 0)
Proof
  conj_tac >> EVAL_TAC >> simp[]
QED

Theorem prefix_audit_exempt_target_and_phi:
  input_vars_from "L" (EL 3 prefix_audit_exempt_fn.fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze prefix_audit_exempt_fn) "J" 0) = ["t"; "a"] /\
  input_vars_from "R" (EL 3 prefix_audit_exempt_fn.fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze prefix_audit_exempt_fn) "J" 0) = ["t"; "b"] /\
  (residual_incoming prefix_audit_exempt_fn 1).ps_stack = [Var "t"; Var "a"] /\
  (residual_incoming prefix_audit_exempt_fn 2).ps_stack = [Var "t"; Var "b"] /\
  (residual_phi prefix_audit_exempt_fn 3
    (residual_incoming prefix_audit_exempt_fn 1)).ps_stack = [Var "t"; Var "x"] /\
  (residual_phi prefix_audit_exempt_fn 3
    (residual_incoming prefix_audit_exempt_fn 2)).ps_stack = [Var "t"; Var "x"] /\
  MEM "t" (live_vars_at (liveness_analyze prefix_audit_exempt_fn) "J" 1)
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem prefix_audit_rejection_cause:
  ~single_use_form prefix_audit_phi_fn /\ ~single_use_form prefix_audit_plain_fn
Proof
  conj_tac >> EVAL_TAC >> simp[]
QED

(* Reachable prefix-origin ledger: three small diamonds were tested.
   The two repeated-ADD variants (plain and independent PHI) successfully
   plan but fail readiness: t is used by a predecessor ADD and the join ADD,
   violating single_use_form. Their computed entry stacks have no residual
   prefix either, so they do not even supply an arbitrary-plan collision.
   The third variant uses exempt ASSIGN in the predecessor. It is ready and
   its analyzed cleanup function plan succeeds. Both predecessor block plans
   start at the actual entry-block result (residual_incoming), not fabricated
   states. Their entire stacks equal the exact input_vars_from join targets:
   [t;a] and [t;b]. Thus the residual prefix is EMPTY, not a smaller chosen
   common suffix. The native PHI endpoints are both [t;x]; t is live after
   PHI, while a/b are incoming-only names and x is the fresh PHI output.

   Outcome is INCONCLUSIVE for universal live-prefix exclusion: no collision
   in this bounded search. The observed exclusion is not proved for all
   joins. Remaining origin obligations separate (i) incoming names, whose
   post-PHI death is given by phi readiness, (ii) fresh PHI outputs, needing
   provenance/freshness relative to the physical residual prefix, and
   (iii) live-through names, whose target coverage does not exclude additional
   lower occurrences. Global single-use and the actual duplication/consumption
   decisions are a potential source for (iii), not an already established
   physical multiplicity theorem. No selective-spill replay invariant or
   frozen-theorem counterexample follows from these fixtures. *)

(* Finite multiplicity ledger. This is the non-JMP, non-halting stage
   sequence; ADD's two candidate orders coincide for [a;a]. No reachability
   claim is made for the overlap input. *)
Definition multiplicity_audit_stages_def:
  multiplicity_audit_stages inst nl ps =
    let operands = compute_operands inst in
    let p1 = SND (emit_input_plan inst.inst_opcode operands nl ps) in
    let p2 = SND (reorder_plan dfg_empty operands p1) in
    let p3 = p2 with ps_stack := stack_pop (LENGTH operands) p2.ps_stack in
    let p4 = FOLDL (\p out. p with ps_stack := stack_push (Var out) p.ps_stack)
                   p3 inst.inst_outputs in
    let p5 = SND (popmany_plan
      (MAP Var (FILTER (\out. ~MEM out nl) inst.inst_outputs)) p4) in
    let p6 = if FILTER (\out. MEM out nl) inst.inst_outputs = [] then p5
             else SND (optimistic_swap_plan dfg_empty inst nl F p5) in
    [ps; p1; p2; p3; p4; p5; p6; release_dead_spills nl p6]
End

Definition multiplicity_audit_counts_def:
  multiplicity_audit_counts op states =
    MAP (\p. (LIST_ELEM_COUNT op p.ps_stack,
               IS_SOME (FLOOKUP p.ps_spilled op))) states
End

Theorem assign_multiplicity_ledger:
  multiplicity_audit_counts (Var "a")
    (multiplicity_audit_stages (mk_inst 0 ASSIGN [Var "a"] ["x"])
      ["a"; "x"] ((init_plan_state 0) with ps_stack := [Var "a"])) =
    [(1,F); (2,F); (2,F); (1,F); (1,F); (1,F); (1,F); (1,F)] /\
  multiplicity_audit_counts (Var "a")
    (multiplicity_audit_stages (mk_inst 0 ASSIGN [Var "a"] ["x"])
      [] ((init_plan_state 0) with ps_stack := [Var "a"])) =
    [(1,F); (1,F); (1,F); (0,F); (0,F); (0,F); (0,F); (0,F)]
Proof
  EVAL_TAC
QED

Theorem add_repeated_multiplicity_ledger:
  multiplicity_audit_counts (Var "a")
    (multiplicity_audit_stages (mk_inst 0 ADD [Var "a"; Var "a"] ["x"])
      ["a"; "x"] ((init_plan_state 0) with ps_stack := [Var "a"])) =
    [(1,F); (3,F); (3,F); (1,F); (1,F); (1,F); (1,F); (1,F)] /\
  multiplicity_audit_counts (Var "a")
    (multiplicity_audit_stages (mk_inst 0 ADD [Var "a"; Var "a"] ["x"])
      [] ((init_plan_state 0) with ps_stack := [Var "a"])) =
    [(1,F); (2,F); (2,F); (0,F); (0,F); (0,F); (0,F); (0,F)]
Proof
  EVAL_TAC
QED

Definition multiplicity_overlap_state_def:
  multiplicity_overlap_state = (init_plan_state 0) with
    <| ps_stack := [Var "a"]; ps_spilled := FEMPTY |+ (Var "a",0) |>
End

Theorem overlap_restore_multiplicity_ledger:
  multiplicity_audit_counts (Var "a")
    [multiplicity_overlap_state;
     SND (do_restore (Var "a") multiplicity_overlap_state)] =
    [(1,T); (2,F)] /\
  multiplicity_audit_counts (Var "a")
    (multiplicity_audit_stages (mk_inst 0 ASSIGN [Var "a"] ["x"])
      ["a"; "x"] multiplicity_overlap_state) =
    [(1,T); (3,F); (3,F); (2,F); (2,F); (2,F); (2,F); (2,F)] /\
  multiplicity_audit_counts (Var "a")
    (multiplicity_audit_stages (mk_inst 0 ADD [Var "a"; Var "a"] ["x"])
      [] multiplicity_overlap_state) =
    [(1,T); (3,F); (3,F); (1,F); (1,F); (1,F); (1,F); (1,F)]
Proof
  EVAL_TAC
QED

Theorem multiplicity_shapes_wf:
  inst_wf (mk_inst 0 ASSIGN [Var "a"] ["x"]) /\
  inst_wf (mk_inst 0 ADD [Var "a"; Var "a"] ["x"]) /\
  inst_wf (mk_inst 0 OFFSET [Lit 0w; Label "L"] ["x"]) /\
  ~inst_wf (mk_inst 0 OFFSET [Var "a"; Label "L"] ["x"])
Proof
  EVAL_TAC
QED

Theorem offset_multiplicity_ledger:
  multiplicity_audit_counts (Var "a")
    [((init_plan_state 0) with ps_stack := [Var "a"]);
     SND (generate_offset_plan
       (mk_inst 0 OFFSET [Lit 0w; Label "L"] ["x"])
       ((init_plan_state 0) with ps_stack := [Var "a"]))] =
    [(1,F); (1,F)] /\
  multiplicity_audit_counts (Var "x")
    [((init_plan_state 0) with ps_stack := [Var "a"]);
     SND (generate_offset_plan
       (mk_inst 0 OFFSET [Lit 0w; Label "L"] ["x"])
       ((init_plan_state 0) with ps_stack := [Var "a"]))] =
    [(0,F); (1,F)]
Proof
  EVAL_TAC
QED

(* Cross-check the ledger endpoint against the native instruction planner,
   including the commutative selection and post-emission stages. *)
Theorem native_multiplicity_endpoints:
  MAP (\(opc, operands, nl, ps).
    (SND (generate_regular_inst_plan ARB dfg_empty ARB ARB
      (mk_inst 0 opc operands ["x"]) nl F F "entry" ps)).ps_stack)
    [(ASSIGN, [Var "a"], ["a";"x"],
       (init_plan_state 0) with ps_stack := [Var "a"]);
     (ASSIGN, [Var "a"], [],
       (init_plan_state 0) with ps_stack := [Var "a"]);
     (ADD, [Var "a"; Var "a"], ["a";"x"],
       (init_plan_state 0) with ps_stack := [Var "a"]);
     (ADD, [Var "a"; Var "a"], [],
       (init_plan_state 0) with ps_stack := [Var "a"]);
     (ASSIGN, [Var "a"], ["a";"x"], multiplicity_overlap_state)] =
    [[Var "a"; Var "x"]; []; [Var "a"; Var "x"]; [];
     [Var "a"; Var "a"; Var "x"]]
Proof
  EVAL_TAC
QED

(* Multiplicity audit conclusion / dependency ledger (bounded, not induction).

   emit_input_plan_live_upper requires ALL_DISTINCT stack, disjoint stack and
   spill domain, and inventory contained in operand_vars operands ++ nl.
   It allows repetitions WITHIN operands: temporary count <= operand count
   + the one live reserve. The ASSIGN and ADD ledgers above exhibit debts
   1 and 2 respectively when a is live; consumption cancels exactly these.
   With a dead, ADD's first a still duplicates because rest contains a.

   emit_reorder_plan_core_live_upper performs that cancellation for a
   materialised selected PERM of operands, LENGTH <=16, from an empty-pending
   residual_budget_wf input, availability and live-inventory coverage.
   reorder_plan_materialised_live_upper additionally exposes the pending
   no-spill, count availability and pending length/stack length hypotheses.
   These results are sufficient accounting interfaces for these two shapes;
   no new variant is needed. emit_reorder_pop_marker_core_live_upper is the
   existing marker-prefix version. They do NOT cover arbitrary deep demand.

   fresh_outputs_residual_budget (Setup) needs ALL_DISTINCT outputs and
   absence of EACH output from both physical stack and spill domain. Here x
   is fresh; output count goes 0 -> 1; dead-output pop removes it, while
   optimistic_swap_plan and release leave a's count unchanged in the ledger.
   residual_budget_wf_optimistic_swap_plan is the existing general budget
   interface. PhiTemporal's phi_origin_stage_count_le and
   phi_origin_schedule_count_le count provenance cells, not a ready-made
   whole-stack uniqueness theorem; this audit does not extend to PHI.

   OFFSET: inst_wf_offset_shape rules out any variable operand, as checked
   above. generate_offset_plan only pushes x and has NO liveness argument:
   it retains x even if x is dead. A live-filtered bound allows that, but a
   global inventory-subset-live claim does not. Freshness of x is necessary.

   Candidate physical live-count<=1 with output freshness is FALSE from
   physical uniqueness alone: overlap_restore_multiplicity_ledger starts
   with ONE physical a plus a spill binding; native_multiplicity_endpoints
   confirms TWO live a survive the complete ASSIGN. This is a fabricated
   local input, NOT evidence of frozen-theorem falsehood or reachability.
   residual_budget_wf base [] rejects it by
   residual_budget_wf_empty_inventory (stack/spill disjointness).

   Smallest next missing premise: establish, at actual reachable restore
   entries, that restoring a live v cannot encounter another physical v
   (and preserve live-count<=1 through the other stages, plus output
   freshness). Stack-plus-spill uniqueness implies this premise and is
   stronger than suffix-exclusion consumers need, but physical uniqueness
   alone cannot be inductive across restore. No conclusion that such
   disjointness holds at joins is licensed by this finite matrix.
*)

Theorem overlap_remaining_multiplicity_ledger:
  multiplicity_audit_counts (Var "a")
    (multiplicity_audit_stages (mk_inst 0 ASSIGN [Var "a"] ["x"])
      [] multiplicity_overlap_state) =
    [(1,T); (2,F); (2,F); (1,F); (1,F); (1,F); (1,F); (1,F)] /\
  multiplicity_audit_counts (Var "a")
    (multiplicity_audit_stages (mk_inst 0 ADD [Var "a"; Var "a"] ["x"])
      ["a"; "x"] multiplicity_overlap_state) =
    [(1,T); (4,F); (4,F); (2,F); (2,F); (2,F); (2,F); (2,F)]
Proof
  EVAL_TAC
QED

Theorem spill_only_multiplicity_ledger:
  multiplicity_audit_counts (Var "a")
    (multiplicity_audit_stages (mk_inst 0 ADD [Var "a"; Var "a"] ["x"])
      ["a"; "x"] (multiplicity_overlap_state with ps_stack := [])) =
    [(0,T); (3,F); (3,F); (1,F); (1,F); (1,F); (1,F); (1,F)] /\
  multiplicity_audit_counts (Var "a")
    (multiplicity_audit_stages (mk_inst 0 ASSIGN [Var "a"] ["x"])
      [] (multiplicity_overlap_state with ps_stack := [])) =
    [(0,T); (1,F); (1,F); (0,F); (0,F); (0,F); (0,F); (0,F)]
Proof
  EVAL_TAC
QED

(* Deep actual-origin candidate 1: distinct live-through targets. *)
Definition deep_origin_names_def:
  deep_origin_names = ["t0";"t1";"t2";"t3";"t4";"t5";"t6";"t7";
    "t8";"t9";"t10";"t11";"t12";"t13";"t14";"t15";"t16"]
End

Definition deep_origin_fn_def:
  deep_origin_fn = mk_raw_function "deep_origin"
    [<| bb_label := "entry"; bb_instructions :=
      MAPi (\i v. mk_inst (100+i) ASSIGN [Lit 1w] [v]) deep_origin_names ++
      [mk_inst 0 JNZ [Lit 1w; Label "L"; Label "R"] []] |>;
     <| bb_label := "L"; bb_instructions :=
      [mk_inst 1 ASSIGN [Var "t0"] ["unusedL"];
       mk_inst 2 JMP [Label "J"] []] |>;
     <| bb_label := "R"; bb_instructions :=
      [mk_inst 3 ASSIGN [Var "t16"] ["unusedR"];
       mk_inst 4 JMP [Label "J"] []] |>;
     <| bb_label := "J"; bb_instructions :=
      MAPi (\i v. mk_inst (200+i) ASSIGN [Var v] [STRCAT "u" v]) deep_origin_names ++
      [mk_inst 5 JMP [Label "exit"] []] |>;
     <| bb_label := "exit"; bb_instructions := [mk_inst 6 STOP [] []] |>]
End

Theorem deep_origin_ready:
  codegen_ready_fn deep_origin_fn /\
  EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb.bb_instructions) deep_origin_fn.fn_blocks
Proof
  EVAL_TAC >> simp[]
QED

Theorem deep_origin_plan_success:
  IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze deep_origin_fn) (dfg_build_function deep_origin_fn)
    (cfg_analyze deep_origin_fn) NONE [] deep_origin_fn 0 0)
Proof
  EVAL_TAC
QED

Definition deep_origin_pre_jump_def:
  deep_origin_pre_jump fn n =
    let bb = EL n fn.fn_blocks in
    SND (THE (generate_inst_plan (liveness_analyze fn)
      (dfg_build_function fn) (cfg_analyze fn) fn
      (HD bb.bb_instructions) (live_vars_at (liveness_analyze fn) bb.bb_label 1)
      F T bb.bb_label (residual_step fn 0 entry_probe_start)))
End

Definition deep_origin_target_def:
  deep_origin_target fn pred = input_vars_from pred
    (EL 3 fn.fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze fn) "J" 0)
End

Theorem deep_origin_entry_stack:
  (residual_step deep_origin_fn 0 entry_probe_start).ps_stack = MAP Var deep_origin_names
Proof
  EVAL_TAC
QED

Theorem deep_origin_entry_state:
  residual_step deep_origin_fn 0 entry_probe_start =
    entry_probe_start with ps_stack := MAP Var deep_origin_names
Proof
  EVAL_TAC
QED


Definition deep_origin_entry_live_def:
  deep_origin_entry_live = FEMPTY |++
    MAP (\i. (("entry",i), REVERSE (TAKE i deep_origin_names))) (REVERSE (COUNT_LIST 19))
End

Definition deep_origin_branch_live_def:
  deep_origin_branch_live (lbl:string) = (FEMPTY : (string # num) |-> string list) |++
    MAP (\i. ((lbl,i),REVERSE deep_origin_names)) [2;1;0]
End

Definition deep_origin_join_live_def:
  deep_origin_join_live = FEMPTY |++
    MAP (\i. (("J",i), REVERSE (DROP i deep_origin_names))) (REVERSE (COUNT_LIST 19))
End

Theorem deep_origin_liveness:
  liveness_analyze deep_origin_fn =
  <| ds_inst := FUNION deep_origin_entry_live
      (FUNION deep_origin_entry_live
      (FUNION (deep_origin_branch_live "R")
      (FUNION (deep_origin_branch_live "L")
      (FUNION deep_origin_entry_live
      (FUNION (deep_origin_branch_live "L")
      (FUNION (deep_origin_branch_live "R")
      (FUNION deep_origin_join_live
      (FUNION (FEMPTY |+ (("exit",1),[]) |+ (("exit",0),[])) FEMPTY))))))));
     ds_boundary := FEMPTY |++ REVERSE
       (MAP (\lbl. (lbl, if MEM lbl ["L";"R";"J"] then REVERSE deep_origin_names else []))
         ["entry";"entry";"R";"L";"entry";"L";"R";"J";"exit"] ++
       MAP (\lbl. (lbl,[])) ["exit";"J";"R";"L";"entry"]) |>
Proof
  EVAL_TAC
QED

Theorem deep_origin_dfg:
  dfg_build_function deep_origin_fn =
  <| dfg_uses := FEMPTY |++ REVERSE
       ([("t0", [mk_inst 1 ASSIGN [Var "t0"] ["unusedL"];
                       mk_inst 200 ASSIGN [Var "t0"] ["ut0"]]);
         ("t16", [mk_inst 3 ASSIGN [Var "t16"] ["unusedR"];
                        mk_inst 216 ASSIGN [Var "t16"] ["ut16"]])] ++
        MAPi (\i v. (v,[mk_inst (200+i) ASSIGN [Var v] [STRCAT "u" v]])) deep_origin_names);
     dfg_defs := FEMPTY |++ REVERSE
       (MAPi (\i v. (v,mk_inst (100+i) ASSIGN [Lit 1w] [v])) deep_origin_names ++
        [("unusedL",mk_inst 1 ASSIGN [Var "t0"] ["unusedL"]);
         ("unusedR",mk_inst 3 ASSIGN [Var "t16"] ["unusedR"])] ++
        MAPi (\i v. (STRCAT "u" v,mk_inst (200+i) ASSIGN [Var v] [STRCAT "u" v])) deep_origin_names);
     dfg_ids := FEMPTY |++ REVERSE
       (MAP (\inst. (inst.inst_id,inst))
         (FLAT (MAP (\bb. bb.bb_instructions) deep_origin_fn.fn_blocks))) |>
Proof
  EVAL_TAC
QED

Theorem deep_origin_cfg:
  cfg_analyze deep_origin_fn =
  <| cfg_succs := FEMPTY |++ REVERSE
       [("exit",[]);("J",["exit"]);("R",["J"]);("L",["J"]);("entry",["R";"L"]);
        ("exit",[]);("J",[]);("R",[]);("L",[]);("entry",[])];
     cfg_preds := FEMPTY |++ REVERSE
       [("exit",["J"]);("J",["L";"R"]);("J",["L"]);("R",["entry"]);("L",["entry"]);
        ("exit",[]);("J",[]);("R",[]);("L",[]);("entry",[])];
     cfg_reachable := FEMPTY |++ MAP (\lbl. (lbl,T)) ["entry";"L";"R";"J";"exit"];
     cfg_dfs_post := ["exit";"J";"R";"L";"entry"];
     cfg_dfs_pre := ["entry";"R";"J";"exit";"L"] |>
Proof
  EVAL_TAC
QED

Theorem deep_origin_pre_jump_left:
  deep_origin_pre_jump deep_origin_fn 1 =
    (entry_probe_start with <| ps_stack := MAP Var deep_origin_names;
       ps_alloc := <| sa_free_slots := [0]; sa_next_offset := 32; sa_spill_base := 0 |> |>)
Proof
  rewrite_tac[deep_origin_pre_jump_def,deep_origin_entry_state,
    deep_origin_liveness,deep_origin_dfg,deep_origin_cfg] >>
  EVAL_TAC
QED

Theorem deep_origin_pre_jump_right:
  deep_origin_pre_jump deep_origin_fn 2 =
    entry_probe_start with ps_stack := MAP Var deep_origin_names
Proof
  rewrite_tac[deep_origin_pre_jump_def,deep_origin_entry_state,
    deep_origin_liveness,deep_origin_dfg,deep_origin_cfg] >>
  EVAL_TAC
QED

Theorem deep_origin_incoming_left:
  residual_incoming deep_origin_fn 1 =
    (entry_probe_start with <| ps_stack := MAP Var (REVERSE deep_origin_names);
       ps_alloc := <| sa_free_slots := [0]; sa_next_offset := 32; sa_spill_base := 0 |> |>)
Proof
  rewrite_tac[residual_incoming_def,deep_origin_entry_state,residual_step_def,
    deep_origin_liveness,deep_origin_dfg,deep_origin_cfg] >>
  EVAL_TAC
QED

Theorem deep_origin_incoming_right:
  residual_incoming deep_origin_fn 2 =
    entry_probe_start with ps_stack := MAP Var (REVERSE deep_origin_names)
Proof
  rewrite_tac[residual_incoming_def,deep_origin_entry_state,residual_step_def,
    deep_origin_liveness,deep_origin_dfg,deep_origin_cfg] >> EVAL_TAC
QED

Theorem deep_origin_targets:
  deep_origin_target deep_origin_fn "L" = REVERSE deep_origin_names /\
  deep_origin_target deep_origin_fn "R" = REVERSE deep_origin_names
Proof
  rewrite_tac[deep_origin_target_def,deep_origin_liveness] >> EVAL_TAC
QED

(* Candidate 2 tests repetition of one selected PHI source. *)
Definition deep_origin_phi_fn_def:
  deep_origin_phi_fn = deep_origin_fn with fn_blocks :=
    MAP (\bb. if bb.bb_label = "J" then bb with bb_instructions :=
      [mk_inst 300 PHI [Label "L";Var "t0";Label "R";Var "t0"] ["p"];
       mk_inst 301 PHI [Label "L";Var "t0";Label "R";Var "t0"] ["q"];
       mk_inst 302 ASSIGN [Var "p"] ["up"];
       mk_inst 303 ASSIGN [Var "q"] ["uq"]] ++
      TL bb.bb_instructions else bb) deep_origin_fn.fn_blocks
End

Theorem deep_origin_phi_rejected:
  ~codegen_ready_fn deep_origin_phi_fn /\
  ~phi_operands_ready deep_origin_phi_fn /\
  ~phi_uses_disjoint (collect_phis (EL 3 deep_origin_phi_fn.fn_blocks).bb_instructions)
Proof
  EVAL_TAC >> simp[]
QED

Theorem deep_origin_branch_live_vars:
  live_vars_at (liveness_analyze deep_origin_fn) "L" 1 = REVERSE deep_origin_names /\
  live_vars_at (liveness_analyze deep_origin_fn) "R" 1 = REVERSE deep_origin_names
Proof
  rewrite_tac[deep_origin_liveness] >> EVAL_TAC
QED

Theorem deep_origin_count_ledger:
  EVERY (\v.
    (LIST_ELEM_COUNT (Var v) (deep_origin_pre_jump deep_origin_fn 1).ps_stack,
     FLOOKUP (deep_origin_pre_jump deep_origin_fn 1).ps_spilled (Var v),
     LIST_ELEM_COUNT v (deep_origin_target deep_origin_fn "L"),
     MEM v (live_vars_at (liveness_analyze deep_origin_fn) "L" 1)) = (1,NONE,1,T) /\
    (LIST_ELEM_COUNT (Var v) (deep_origin_pre_jump deep_origin_fn 2).ps_stack,
     FLOOKUP (deep_origin_pre_jump deep_origin_fn 2).ps_spilled (Var v),
     LIST_ELEM_COUNT v (deep_origin_target deep_origin_fn "R"),
     MEM v (live_vars_at (liveness_analyze deep_origin_fn) "R" 1)) = (1,NONE,1,T) /\
    (LIST_ELEM_COUNT (Var v) (residual_incoming deep_origin_fn 1).ps_stack,
     FLOOKUP (residual_incoming deep_origin_fn 1).ps_spilled (Var v),
     LIST_ELEM_COUNT (Var v) (residual_incoming deep_origin_fn 2).ps_stack,
     FLOOKUP (residual_incoming deep_origin_fn 2).ps_spilled (Var v)) = (1,NONE,1,NONE))
    deep_origin_names
Proof
  rewrite_tac[deep_origin_pre_jump_left,deep_origin_pre_jump_right,
    deep_origin_incoming_left,deep_origin_incoming_right,deep_origin_targets,
    deep_origin_branch_live_vars] >> EVAL_TAC
QED

(* Output shadow acceptance: p is arbitrary, including copies of out.
   Pushing creates a nearer occurrence; removing it does not search p. *)
Theorem output_shadow_push_pop:
  !ps p core out.
    popmany_plan [Var out]
      (ps with ps_stack := stack_push (Var out) (p ++ core)) =
    ([SOPop 1], ps with ps_stack := p ++ core)
Proof
  rpt gen_tac >>
  `stack_get_depth (Var out) (stack_push (Var out) (p ++ core)) = SOME 0` by
    simp[stack_get_depth_def, stack_push_def, listTheory.REVERSE_SNOC, stack_find_def] >>
  `stack_get_depth (Var out)
     (ps with ps_stack := stack_push (Var out) (p ++ core)).ps_stack = SOME 0` by
    simp[] >>
  drule popmany_plan_top_singleton >>
  simp[stack_pop_def, stack_push_def, rich_listTheory.TAKE_SNOC,
       TAKE_APPEND, TAKE_LENGTH_TOO_LONG]
QED

(* The scheduled live value is physically in the suffix. The prefix may
   contain BOTH the scheduled name and the new output name. *)
Theorem output_shadow_optimistic_core_hit:
  !ps p a out.
    a <> out /\ ~operand_equiv dfg_empty (Var out) (Var a) ==>
    optimistic_swap_plan dfg_empty (mk_inst 0 ISZERO [] [out]) [a] F
      (ps with ps_stack := p ++ [Var a; Var out]) =
    ([SOSwap 1], ps with ps_stack := p ++ [Var out; Var a])
Proof
  rpt strip_tac >>
  simp[optimistic_swap_plan_def, mk_inst_def,
       stack_get_depth_def, REVERSE_APPEND, stack_find_def,
       do_swap_def, stack_swap_def, top_n_def, stack_pop_def,
       TAKE_APPEND, DROP_APPEND, stack_push_def, stack_peek_def,
       EL_APPEND2, LUPDATE_APPEND2, LUPDATE_def] >>
  EVAL_TAC
QED

(* Output-shadow consumer ledger (refines the earlier exclusion audit).

   output_shadow_push_pop is symbolic in the entire prefix AND old core,
   with no output absence premise anywhere. In particular p=[Var out] and
   an out-free core give the requested stale runtime output test. The
   newly inserted output shields its own singleton dead-output pop. The
   resulting operations and allocator are identical for any p and q; only
   the untouched lower stacks differ. This is not total output uniqueness.
   For several distinct outputs the analogous removal needs occurrence
   shielding at each sequential request; the old DISJOINT-prefix inventory
   pop lemmas do not supply that result when prefixes contain outputs.
   We do NOT claim a general multi-output replay theorem from this test.

   Post-emission stage        canonical counts / core / runtime observations
   ----------------------------------------------------------------------
   MAP Var outputs push      For counts at most one in core, outputs distinct
                             and absent from core suffice. The common spill
                             domain must also lack outputs for core+spill
                             resource at most one. A runtime stale copy in p
                             adds to TOTAL count, not the common-core count.
                             Push itself does not inspect spills or prefix.
   dead-output pop           Actual singleton output pop is shielded by the
                             just-pushed top occurrence, as checked above.
                             No spill absence is needed for the operation.
                             Canonical resource accounting still needs the
                             separate count boundary, not just this frame.
   optimistic swap           Disabled tests use only shared inst/nl/term/dfg.
                             Enabled branch queries Var(LAST nl), NOT outputs
                             in general. output_shadow_optimistic_core_hit
                             checks the hit case with arbitrary prefix copies
                             of BOTH query and output. Its non-equivalence
                             premise selects the actual swap branch; equiv
                             selects a no-op independently of stack/prefix.
                             Mere common spill availability is insufficient:
                             LowerPrefix.optimistic_swap_prefix_obstruction
                             already checks the absent-core countercase.
                             StageAudit.optimistic_producer_spills_query_probe,
                             enabled_query_probe, native_ops_probe strengthen
                             it through actual preparation: a formerly core
                             query can be spilled, exposing a hidden live name.
                             Therefore initial core-hit coverage alone is NOT
                             a preservation theorem for this tail consumer.
   release_dead_spills        Shared maps and allocators give same deletion
                             list and frees. Stack is untouched. Reuse Setup's
                             release_fold_stack_update (implementation frame)
                             and Inventory.release_dead_spills_stack. Output
                             absence from spills matters for resource bounds,
                             not equality of the two release computations.
   successor cleanup         Not part of regular tail, but next block setup.
                             Reuse Inventory.clean_stack_plan_prefix_replay:
                             its layout/input depth and branch-coordination
                             premises remain required. Core-relative output
                             freshness alone says nothing about them. Cleanup
                             can inspect residual names and total LENGTH.

   Conclusion limited to this test: TOTAL runtime output absence is not
   needed by push or a just-created singleton dead-output pop, and need not
   be postulated merely to frame these operations. Core-relative freshness
   is adequate for the proposed core resource count, provided spill absence
   is separately produced. Full replay still requires query shielding after
   selective spill, multi-output pop shielding, cleanup branch coordination,
   common spill/allocator layout, and the canonical resource producers. None
   follows from SSA alone or from an arbitrary equal suffix. These local
   observations do not certify reachability or refute the frozen theorem.
*)

(* Stable accounting coverage audit (C3.resources.producers.accounting).

   R(x,p) = count x p.ps_stack + indicator(x IN FDOM p.ps_spilled).
   Two DIFFERENT obligations are under review:
     U: R(Var v,p)<=1 for demand-live v at a stable position;
     Z: R(Var v,p)=0 immediately before v is defined again.
   Neither is asserted universally by this ledger. All items below are
   sufficient-premise interfaces or remaining proof obligations.

   Transition             Sufficient premises / checked interface / gap
   ----------------------------------------------------------------------
   Ordinary non-JMP       Setup.native_regular_next_live_upper proves U at
                          return given operand+next-live U at input, operand
                          availability, <=16 operands, distinct fresh outputs.
                          It does NOT produce its own output-absence premise.
                          Internal input duplication spends consumption debt:
                          Inventory.emit_input_plan_relevant_variable_upper
                          bounds R(v) by count(v,operands)+indicator(v in nl).
                          Bounded materialised reorder supplies an exact suffix.
                          selected_suffix_resource_extinction now checks the
                          arithmetic cancellation: R<=count(selected) plus
                          exact suffix implies zero after consuming it, including
                          spill absence. Thus last-use extinction requires
                          v NOTIN nl, initial pointwise U, materialisation and
                          a bounded successful reorder, not blanket live support.
                          Subsequent output pushes must not recreate v; SSA can
                          discharge this at a DIFFERENT definition position.
                          regular_post_emit_tail_resource_nonincrease then
                          preserves zero. If v was never an operand on this path,
                          this last-use argument supplies no extinction event.

   OFFSET                 generate_offset_plan pushes output unconditionally
                          for a Label offset target; it does not consume inputs,
                          pop a dead output, or release dead spills. U for the
                          new output needs Z at entry. Other counts unchanged.
                          offset_multiplicity_ledger already checks duplication
                          from a stale output. offset_outputs_used guarantees a static
                          use, NOT that a chosen runtime path executes that use
                          before revisiting the definition. The unused-path case
                          must instead cross a demand-killing branch/PHI event.

   PHI                    NONE selection is identity. A present dead source is
                          renamed in place; a live source is duplicated first.
                          To derive U: selected-source availability, <=1 old
                          source resource, fresh output, valid selected depth,
                          and accounting for deep do_dup spill effects are needed.
                          To derive Z for the source on its last PHI use: source
                          not next-live and unique physical occurrence plus no
                          spill occurrence. PhiTemporal's selected_extinction
                          removes a UNIQUE selected ORIGIN in the keep=F branch;
                          it does not erase arbitrary same-name lower cells.
                          If keep=T the old selected origin explicitly survives.
                          Sequential PHIs require evolving selection/liveness,
                          not a simultaneous global renaming assumption.

   spill / restore        do_spill_at_resource_nonincrease transports an upper
                          bound (can overwrite an existing map binding).
                          do_restore removes one map entry and pushes one cell:
                          R is conserved, even if the stack already has copies.
                          Neither operation proves Z; zero persists if no other
                          stage creates the name. Selective spilling can remove
                          the COMMON stack occurrence of an optimistic query;
                          resource existence in spills is not query shielding.

   JMP / join             Successful join_reached establishes a target suffix;
                          analyzed_terminal_jmp_target_coverage supplies target
                          availability from predecessor live-out coverage. It
                          supplies no total count U for deep reorder and does not
                          delete non-target residual names. For an entry-live
                          name present in the target suffix, total U would exclude
                          it from the prefix. Missing: reachable total U and
                          PHI projection/count transport, NOT suffix existence.

   cleanup (all branches) Zero and upper counts survive any stack-only pop or
                          Var-to-marker change; spilled counts are unchanged.
                          Extinction of a particular name additionally requires
                          ALL its stack copies be popped/marked and spill absence.
                          preds <> [pred]: identity, no strict decrease.
                          single pred with <=1 succ: identity, no strict decrease.
                          missing pred block: identity (unreachable under lookup
                          premises still to be supplied globally).
                          branch, NULL inputs and ok: all stack Vars marked;
                          spilled copies are NOT erased by this operation.
                          branch, nonempty inputs and ok: pop physical to_cleanup,
                          mark retained; to_pop is drawn only from predecessor
                          layout. Need v in layout and all-copy coverage.
                          branch, not ok: pop MAP Var to_pop; one request per
                          layout occurrence, not an all-copy eraser. U before
                          cleanup would make one successful removal sufficient.
                          A stale name outside layout need not be removed.

   NOP / params /         Identity cases preserve established bounds but cannot
   straight-line edges    manufacture Z. Entry parameter seeding is separate:
                          initial_parameter_origins accounts for names, while
                          count/distinctness still needs the parameter interface.
                          A halting block may retain a dead singleton regular/PHI
                          output; it has no runtime successor in a valid path.
                          Do not claim intermediate exact live support there.

   Path-induction gap and measure:
   Trace a FIXED name from its previous dynamic definition to its next dynamic
   definition along a finite execution-path segment. Induct on the number of
   remaining instruction/edge events (strictly decreases at every transition),
   not on R, which need not decrease across identities/spills/restores. Between
   definitions the desired resource is nonincreasing except temporary input/PHI
   debt, discharged at stable returns under the interfaces above. To get zero,
   a separate demand-loss cut must prove that this segment contains either a
   last-use consumption/rename event or branch cleanup covering the old name,
   before redefinition. It must also cover paths that SKIP every static use.
   No-cleanup edges have no deletion event and so cannot close that argument.
   The cut needs liveness transport, SSA dominance, PHI edge demand and actual
   path reachability together; static demand origin alone is insufficient.

   Existing interval_live_origin / interval_computed_query_origin and their
   prefix-exclusion corollaries in Callers split a query into entry-live or a
   definition since the boundary. They do not prove that an old copy is absent
   at that definition, and do not preserve stack query shielding after spilling.
   Canonical DFS visited-event induction proves a different freshness question
   (first compilation); runtime revisits cannot reuse that argument unchanged.

   Audit outcome: local cancellation and preservation are compatible with the
   candidate, but the first-surviving-copy cut, deep JMP count transport, PHI
   resource accounting and query shielding remain unproved. This is neither a
   certified universal invariant nor a frozen-theorem counterexample. No new
   fixture enumeration or global invariant definition was used for this audit.
*)

(* First-reactivation / demand-loss causal audit (C3.gate.reset_cut).

   Scope and logical boundary:
   E0341's self-carried PHI candidate is NOT ready. E0342's
   analyzed_phi_incoming_first_reactivation is a universal logical boundary:
   for incoming v used by PHI i and live at j, it provides i<k<j defining v,
   and deadness at every boundary i<r<=k. It does not provide a resource
   premise at any of those boundaries. Its premises alone do NOT include
   SSA, canonical parameters or instruction well-formedness. The following
   classification additionally uses the frozen theorem's codegen_ready_fn.

   First defining instruction k (classification argument, not new theorem):
   * inst_defs is inst_outputs (venomInst). NOP and output-free terminators
     cannot be k under inst_wf. Parameter definitions are confined to the
     entry prefix by canonical_param_prefix; a block containing PHIs cannot
     be entry by block_entries_ready. They cannot be k in this situation.
   * PHIs form a prefix by bb_well_formed. A later PHI defining v cannot
     explain live v at j: if j is in the prefix, incoming-dead-after already
     forbids it; otherwise propagate back to the prefix end. SSA gives no
     further definition of v after k, and phi_block_ready forbids v live at
     that end. This is a logical exclusion argument still requiring formal
     packaging if used by a consumer. It is not a physical erasure argument.
   * Remaining k is OFFSET or an output-producing regular instruction,
     INCLUDING ASSIGN. generate_inst_plan dispatches ASSIGN to the regular
     pipeline. Unlowered opcodes are rejected by readiness. The single-use
     property does not exclude these routes: ASSIGN, PHI, OFFSET and params
     are exempt in sue_count_exempt; a counted use can be skipped by a path.

   Old incoming occurrence at the earlier PHI entry: two different routes.
   Route                    Last demand / actual potential deletion event
   ----------------------------------------------------------------------
   Selected on this edge    input_vars_from selects this PHI source. At PHI
                            execution the source ceases to be live after its
                            use (E0342's i+1 fact); generate_phi_plan's keep=F
                            branch overwrites ONE selected depth. Existing
                            phi_origin_stage_selected_extinction removes a
                            UNIQUE selected tag, not every cell named v. A
                            spill must also be absent/restored consistently.
                            Needed entry bound is total R(v)<=1 plus actual
                            source availability, not one tagged origin alone.
   Only another edge        input_vars_from replaces this input by this
                            edge's selected source; no PHI step selects v.
                            Follow the finite path backwards to the first
                            loss of edge demand since v's previous dynamic
                            definition. If an ordinary last use intervenes,
                            the existing suffix resource cancellation applies
                            with its entry bound. If every use was skipped,
                            the cut must be a divergent successor choice with
                            v in predecessor live-out but not chosen inputs.
                            clean_stack_plan acts at a single-predecessor
                            branch successor. With several predecessors its
                            identity branch deletes nothing; ready join
                            predecessors must end in JMP, so a proof must
                            locate an EARLIER divergent edge, not claim the
                            final JMP reorder removes non-target names.

   Exact outstanding physical implication (NOT asserted here):
   For a genuine native path segment between consecutive dynamic definitions
   of v, entered with zero old resources before the first definition, produce
   stable pointwise U for relevant operands and live names. At its first
   demand-loss cut prove R(v,q)=0 from the actual native result p -> q:
     - selected PHI: availability + U at p, dead selected source and valid
       selected depth must imply no Var v in q.ps_stack or q.ps_spilled;
     - ordinary last use: U, materialisation, bounded exact operand suffix,
       not-next-live, and no v output permit selected_suffix_resource_extinction;
     - skipped-use branch: v in layout but not inputs, U at p, and actual
       clean_stack_plan result must remove/mark its unique physical cell;
       any map occurrence needs its OWN release argument. Cleanup does not
       release spills, and OFFSET/PHI may not do so either. If no stack cell
       exists, a surviving spill cannot be treated as zero automatically.
   Then transport zero through the remaining dead interval to k, proving no
   other step recreates v (SSA and exact stage behavior). The regular U
   interface requires output absence, so assuming U at every reachable point
   to obtain this reset would be circular unless a joint path invariant and
   the demand-loss cut are independently proved. E0342 supplies neither the
   preceding dynamic definition nor the cut across CFG edges.

   At k / first subsequent observable query:
   Regular (ASSIGN too) pops the operand window, pushes output v, and may
   query LAST next_liveness in optimistic_swap immediately. It never sweeps
   old v cells. A later emit_one_input exact depth lookup or optimistic query
   can expose an old v when the new copy spills (the checked selective-spill
   obstruction above). OFFSET pushes without input consumption, dead-output
   removal or spill release; its first later depth query has the same gap.
   No surviving PHI-k case is justified by the logical classification above;
   for general cross-block redefinitions PHI's selected-origin accounting
   still needs its entry uniqueness premise.

   Alias check: the analyzed DFG records the unique static ASSIGN definition;
   normalize_operand follows its singleton input recursively, with a visited
   guard, and operand_equiv compares the resulting roots (dfgDefs). Thus
   ASSIGN v:=Var w may make v and w equivalent for reorder/optimistic elision;
   v:=Lit c may normalize v to that literal. This is not name erasure:
   emit_one_input and optimistic_swap's selected depth query use exact operand
   equality. No assumption that dfg_empty models this route is justified.
   Static dominance ensures the definition of an incoming v is available at
   its NAMED predecessor endpoint, not that all dynamic paths execute its
   use before revisiting the defining block. A same-block later regular or
   OFFSET definition can supply a backedge operand; E0341 rules out only
   the direct PHI-output self-input live-after-prefix construction.

   Strategy decision: unresolved. The feasible remaining route requires a
   previous dynamic ordinary/ASSIGN/OFFSET definition, a selected-source or
   skipped-use demand-loss cut, a surviving residual resource at that cut,
   and a later exact query exposed after selective spill. No ready native
   witness or universal exclusion has been established. Do not launch more
   fixtures or export a conditional consumer on this audit's authority.
*)
