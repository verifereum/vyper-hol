# TASK: Cross-block DFG alias invariant of the codegen block induction (lineage_alias_successor)

## Meta
Status: planned
Priority: P0
Created: 2026-11-05
Location: venom/codegen/proofs/fnAliasInvScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

```sml
Theorem lineage_alias_successor:
  !fuel ctx lo liveness dfg cfg ch growth spill_base lbl_ctr fn lbl bb ps h
   promised block_ops ps_after ra vs vs'.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    retpc_shape_ok fn /\ opaque_use_ok fn /\
    lineage_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps /\
    vs.vs_current_bb = lbl /\
    (!l. FLOOKUP vs.vs_labels l = OPTION_MAP n2w (FLOOKUP lo l)) /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan liveness dfg cfg fn bb
      (ps with <| ps_cleanup_height := h; ps_cleanup_promised := promised |>) =
      SOME (block_ops, ps_after) /\
    (!pred x. vs.vs_prev_bb = SOME pred /\
       MEM x (input_vars_from pred bb.bb_instructions
                (live_vars_at liveness lbl 0)) ==>
       MEM (Var x) ps.ps_stack \/ Var x IN FDOM ps.ps_spilled) /\
    (!at. MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled ==>
       operand_val (frame_view fn ra vs) lo at =
       operand_val (frame_view fn ra vs) lo (normalize_operand dfg [] at)) /\
    run_block fuel ctx bb vs = OK vs' /\ ~vs'.vs_halted
    ==>
    !at. MEM at ps_after.ps_stack \/ at IN FDOM ps_after.ps_spilled ==>
      operand_val (frame_view fn ra vs') lo at =
      operand_val (frame_view fn ra vs') lo (normalize_operand dfg [] at)
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build fnAliasInvTheory` passes, with no CHEAT in fnAliasInv or in any theory you add.
2. The statement above is byte-for-byte unchanged in `venom/codegen/proofs/fnAliasInvScript.sml`.
3. No duplicate or near-duplicate lemmas: search before adding one; each helper exists once in its most general form.

**If the theorem is false as stated:** give a concrete counterexample (a function, a lineage state, a run) and the tightest sufficient fix. Do NOT weaken the statement.

## Build

```
cd <this directory>
holbuild -j4 build fnAliasInvTheory
```

## Background

The codegen proof (Venom IR to EVM assembly) proves `gen_fn_frame_simulation` (venom/codegen/venomToAsmPropsScript.sml) by induction over blocks. One premise of each block step is the DFG alias invariant: every operand on the stack planner's stack or in its spill map has the value of its ASSIGN-chain root (`normalize_operand dfg [] at`), read through the frame view. The planner's alias-only reorder steps rely on it. This theorem re-establishes the invariant after one block runs, for the stack and spill map that block's code leaves (`ps_after`), which the successor's lineage state carries (`lineage_entry`).

A lineage state (`lineage_state`, venom/codegen/proofs/fnPlanLineageScript.sml) is the planner state of a run-time CFG path: the DFS-planned successor state with the stack and spill map the predecessor's code left. The SML comments above the statement explain why the theorem should hold.

## Domain Constraints

- holbuild only. Never `holbuild run` or `holbuild repl`; probe with scratch lemmas ending in `cheat` and rebuild.
- Never raise the tactic timeout (no `--tactic-timeout`, no `tactic_timeout` in holproject.toml). A step over 2.5 s is a performance bug: split it.
- No `TRY`/`ORELSE` around metis or other proof search; select goals with `>~`, `>-`, `>|`.
- No `cheat` left anywhere, no new axioms, no `let` in theorem statements.
- Don't edit `semantics/`, `frontend/`, `lowering/`, `venom/defs/`, `venom/compiler/`, `venom/passes/`, `venom/analysis/` or `venom/codegen/defs/`: the theorem is about those definitions as they are. Don't edit other theories in `venom/codegen/proofs/` either, except `fnAliasInvScript.sml`.
- Put helpers in `fnAliasInvScript.sml` or in new leaf theories next to it in `venom/codegen/proofs/` (e.g. `fnAliasInv*Script.sml`), registered in holproject.toml the way neighbouring theories are if needed. Don't mark a helper `[local]` if other theories could use it.
- A `[local]` lemma you need from another theory (e.g. `dominates_path_no_revisit`): restate it in your leaf only if you cannot import it; prefer importing exported lemmas.
- `lineage_state_block_plan` (fnPlanLineage) is admitted on this branch and is being proved elsewhere; you may use it, but nothing in this theorem obviously needs it.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Target | venom/codegen/proofs/fnAliasInvScript.sml | statement + intuition comments |
| Lineage states | venom/codegen/proofs/fnPlanLineageScript.sml | `dfs_aux_call`, `dfs_block_state`, `lineage_state`, `lineage_entry`, `lineage_state_dfs_fields` |
| Planner | venom/codegen/defs/stackPlanGenScript.sml | `generate_block_plan`, `generate_regular_inst_plan`, `generate_phi_plan`, `clean_stack_plan`, JMP join reorder, `codegen_ready_fn` (line ~447), `block_entries_ready`, `phi_operands_ready`, `dead_stack_marker`, `init_cleanup_plan_state`, `generate_fn_plan_aux`, `generate_succs_plan` |
| Stack ops | venom/codegen/defs/stackPlanOpsScript.sml, venom/codegen/defs/stackPlanTypesScript.sml | `reorder_one`, `stack_swap`, spill/restore, `release_dead_spills` |
| Plan-state facts | venom/codegen/proofs/planWfScript.sml, planSpillBoundsScript.sml, allocMonoScript.sml, planAlignScript.sml, fnPlanDecompScript.sml | existing facts about plan states and the function planner |
| DFG | venom/analysis/dfg/defs/dfgDefsScript.sml, venom/analysis/dfg/dfgAnalysisPropsScript.sml | `normalize_operand`, `dfg_build_function`, `normalize_operand_eval_restricted` |
| Liveness | venom/analysis/liveness/defs/livenessDefsScript.sml, venom/analysis/liveness/livenessAnalysisPropsScript.sml, venom/analysis/liveness/proofs/ | `live_vars_at`, `input_vars_from`, `liveness_analyze`; `liveness_sound` (witness paths), `live_vars_at_uses`, `live_vars_at_transfer` |
| CFG / dominance | venom/analysis/cfg/defs/cfgDefsScript.sml, venom/analysis/cfg/cfgAnalysisPropsScript.sml, venom/codegen/defs/codegenReadyComputeScript.sml, venom/proofs/venomExecProofsScript.sml | `cfg_analyze`, `cfg_succs_of`; `fn_dominates_cfg_analyze`; `fn_dominates_predecessor` |
| Dominance path lemma | venom/passes/remove_unused/proofs/removeUnusedProofsScript.sml (~line 1736) | `dominates_path_no_revisit` (`[local]` there) |
| Well-formedness | venom/defs/venomWfScript.sml | `def_dominates_uses`, `ssa_form`, `wf_function` |
| Execution | venom/defs/venomExecSemanticsScript.sml, venom/proofs/venomExecProofsScript.sml | `run_block`, `eval_one_phi`; `exec_block_preserves_non_output_vars` |
| Frame view | venom/codegen/defs/frameRelScript.sml, venom/codegen/defs/codegenRelScript.sml, venom/compiler/unitShapeDefsScript.sml | `frame_view`, `operand_val`, `frame_view_vars_lookup`, `frame_view_non_retpc`, `retpc_shape_ok`, `opaque_use_ok`, `copy_phi_var` |
| ASSIGN-root lemma | venom/codegen/proofs/fnFrameStepsRevertForwardScript.sml | `normalize_operand_codegen_assign` (that theory may not build on this branch: read, don't import) |
| Consumer | venom/codegen/venomToAsmPropsScript.sml, venom/codegen/proofs/fnBlockStepScript.sml, venom/codegen/proofs/fnFrameStepsScript.sml | how the alias premise is used |

## Notes

- A statement check found no counterexample. The proof needs a static invariant of lineage states (names on a lineage stack/spill map are live out of the lineage predecessor; vars live along that edge are all held); nothing proves it yet.
- An earlier, unfinished run on `lineage_state_block_plan` built related planner-inventory lemmas (`lineage_inventory`, `fnPlanLineageInventoryScript.sml`, `fnPlanLineageDemandSupportScript.sml`, `fnPlanLineagePathScript.sml`) on git ref `origin/bot/opus/seq-507-lineage`, off an older base. If your git tool allows `git show <ref>:<path>`, read them for ideas; don't merge that branch.
