# TASK: Successor transfer for the codegen block induction, after the join-spill fix (lineage_state_block_plan)

## Meta
Status: planned
Priority: P0
Created: 2026-11-04
Location: venom/codegen/proofs/fnPlanLineageScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

```sml
Theorem lineage_state_block_plan:
  !liveness dfg cfg ch growth spill_base lbl_ctr fn fn_ops ps_end lbl bb
   ps ps_dfs block_ops ps_dfs_after.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lineage_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps_dfs /\
    generate_block_plan liveness dfg cfg fn bb ps_dfs =
      SOME (block_ops, ps_dfs_after)
    ==>
    ?h promised ps_after.
      generate_block_plan liveness dfg cfg fn bb
        (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
        SOME (block_ops, ps_after) /\
      ps_after.ps_alloc = ps_dfs_after.ps_alloc
```

The definitions it uses (`dfs_aux_call`, `dfs_succs_call`, `dfs_block_state`,
`lineage_state`) are in the same file and are frozen too.

**Do not modify this statement or those definitions.** Prove it as-is, or produce a counterexample.

(*
 ************************************************************
 * DO NOT START THIS PROOF until you have finished and
 * validated ALL the machinery you will need for it.
 * Especially machinery that can be generalized and shared
 * between proofs — write it in separate helper files
 * and build them first.
 *
 * Building generic, powerful abstractions (lemmas, tactics,
 * conversions) that help this proof IS explicitly in scope.
 ************************************************************
 *)

## Completion Criteria

1. `holbuild --gcthreads 8 -j4 build fnPlanLineageTheory` passes with zero CHEAT warnings and zero failures.
2. No duplicate or near-duplicate lemmas: each helper exists once, in its most general form. Search the existing theories (below) before proving a fact.
   Owner-approved exception: you may not edit theories outside the `fnPlanLineage*` family (reorderSim, fnAliasStep, fnFrameStepsRevertForward and every other theory owned by another piece stay unchanged). When you need a fact proved in such a theory and importing it would pull frame-level theories into the planner leaves or close an import cycle, put one exact copy (same statement) of it, and of any helper lemmas its proof needs, in a `fnPlanLineage*` leaf, with a comment naming the original theory. This is a standing approval for every such copy, not only the ones listed: no further owner permission is needed. Copies made so far: `list_elem_count_dom_length`, `available_input_plan_length` (from fnFrameStepsRevertForward), `generate_emit_ops_slots`, `popmany_plan_inventory_subset`, `optimistic_swap_plan_inventory_subset`, `release_dead_spills_inventory_subset` (from fnAliasStep). Such a copy satisfies this criterion; list each one in the commit message that adds it.
3. New helper theories, if any, are registered in `holproject.toml` the way the existing ones are.

**If the theorem is false as stated:**
- Produce a HOL4 counterexample (concrete function, `EVAL`).
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
cd <this directory>
holbuild --gcthreads 8 -j4 build fnPlanLineageTheory
```

Always pass `--gcthreads 8` (a Poly/ML GC assertion fails without it on this host).

## Background

vyper-hol's Venom-to-EVM code generator plans stack layouts with a DFS
over the CFG (`generate_fn_plan_aux` / `generate_succs_plan`): each block
is planned once, from the planner state its first-visited predecessor left.
At run time a block can be entered from any predecessor, carrying a
different stack. The block-level simulation (`gen_fn_frame_simulation`,
venom/codegen/proofs/venomToAsmPropsScript.sml) runs on `lineage_state`s,
the planner state of the path actually taken. This theorem says the code
the block was compiled to is also what the planner would emit from the
run-time path's state (up to the cleanup bookkeeping fields), so the
simulation can step through any CFG path.

`codegen_ready_fn` (venom/codegen/defs/stackPlanGenScript.sml) was
strengthened so this holds: `block_entries_ready` (the entry block has no
predecessors; every predecessor of a block with several predecessors ends
in JMP) and `phi_operands_ready`. Notes on why it holds are in SML
comments above the theorem.


### Earlier run and the planner fix

An earlier run of this theorem (its files are `PLAN_lineage_block_plan.md`,
`STATE_lineage_block_plan.md` and `LEARNINGS_lineage_block_plan.md` here;
read the LEARNINGS) certified a counterexample: a diamond with 17 values
live across the branch, where the JMP join reorder restored spilled
targets lazily, `stack_swap` saturated, and the two predecessors entered
the join with different stacks. That was a real miscompile, and the
planner has been fixed the way the Python compiler does it:

- the JMP path of `generate_regular_inst_plan` restores every spilled join
  target before the reorder (`restore_spilled_plan` in stackPlanOps,
  `join_target_ops` in stackPlanGen);
- `generate_inst_plan` returns NONE for a JMP whose final stack does not
  end in the join's target operands (`join_reached`).

So that counterexample now makes the plan NONE. What the earlier notes
say about the join reorder predates the fix; their other findings still
apply. Helper lemmas the earlier run proved are in
`venom/codegen/proofs/fnPlanLineageReplayScript.sml`: reuse them.

A statement check after the fix found no counterexample. It expects the
proof to need a static invariant of plan states (the SML comments above
the theorem describe one) and liveness convergence for "the predecessor's
live-out is the join's target set".

## Domain Constraints

- holbuild only (no Holmake, no `holbuild run`/`repl`). Probe with scratch lemmas ending in `cheat` and rebuild.
- Never raise the tactic timeout (no `--tactic-timeout`, no holproject edits to it). A step that runs over 2.5 s must be split.
- No `TRY`/`ORELSE` around metis or other search.
- No `cheat` left anywhere you touched; no new axioms; no `let` in theorem statements.
- Do not edit the planner or analysis definitions (`venom/codegen/defs`, `venom/analysis`); the theorem is about them as they are.
- Keep helpers in `venom/codegen/proofs/` (a new `fnPlanLineage*Script.sml` is fine).

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Planner | venom/codegen/defs/stackPlanGenScript.sml | `generate_block_plan`, `generate_fn_plan_aux`, `generate_succs_plan`, `generate_fn_plan_with_cleanup_analyzed`, `clean_stack_plan`, `generate_phi_plan`, JMP join reorder in `generate_regular_inst_plan`, `release_dead_spills`, `codegen_ready_fn`, `block_entries_ready`, `phi_operands_ready`, `dead_stack_marker` |
| Stack ops | venom/codegen/defs/stackPlanOpsScript.sml, stackModelScript.sml | `reorder_one`, `stack_swap`, `stack_get_depth`, `stack_get_phi_depth`, spill/restore |
| Liveness defs | venom/analysis/liveness/defs/livenessDefsScript.sml | `live_vars_at`, `input_vars_from`, `liveness_analyze` |
| Liveness facts | venom/analysis/liveness/livenessAnalysisPropsScript.sml; venom/analysis/liveness/proofs/ (livenessConvergenceProofs, livenessTransferProofs, livenessSoundProofs, ...) | transfer, propagation across blocks, convergence (`liveness_recompute_convergence`) |
| CFG | venom/analysis/cfg/defs/cfgDefsScript.sml, venom/analysis/cfg/cfgAnalysisPropsScript.sml | `cfg_analyze`, `cfg_preds_of`, `cfg_succs_of`, `cfg_is_normalized` |
| Well-formedness | venom/defs/venomWfScript.sml | `wf_function`, `inst_wf`, `def_dominates_uses`, `ssa_form` |
| Earlier helpers | venom/codegen/proofs/fnPlanLineageReplayScript.sml | lemmas proved by the earlier run |
| Planner decomposition | venom/codegen/proofs/fnPlanDecompScript.sml | existing facts about the function planner's recursion |
| Planner state facts | venom/codegen/proofs/planWfScript.sml, planSpillBoundsScript.sml, allocMonoScript.sml, planAlignScript.sml | well-formedness, alloc monotonicity, spill bounds of plan states |
| Codegen relation | venom/codegen/defs/codegenRelScript.sml | how dead_stack_marker entries are treated |

## Notes

- A statement check found the two counterexamples that motivated `block_entries_ready` (entry block with a predecessor; a join predecessor ending in `jnz c,@J,@J`). With it, and with the join-spill fix above, no counterexample is known.
- `generate_block_plan` does not fail on an operand absent from the stack; it skips it. So equality of DFS and lineage code needs a static invariant of plan states (see the SML comments), not only SOME-ness.
- Possible corner: `Label ""` equals `dead_stack_marker`; the hypothesis excluding marker operands is there for it.
