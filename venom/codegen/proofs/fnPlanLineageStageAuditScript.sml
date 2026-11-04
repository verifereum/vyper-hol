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
