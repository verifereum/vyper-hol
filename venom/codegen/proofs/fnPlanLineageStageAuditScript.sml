Theory fnPlanLineageStageAudit
Ancestors
  fnPlanLineageInventory fnPlanLineageReplay stackPlanGen stackPlanOps venomInst

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
