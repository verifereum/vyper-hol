# TASK: The stack at a join block's entry (lineage_entry_join_stack)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/codegen/proofs/fnPlanLineageJoinScript.sml

## Theorem Statement (FROZEN)

In `venom/codegen/proofs/fnPlanLineageJoinScript.sml`:

```sml
Theorem lineage_entry_join_stack:
  !liveness dfg cfg fn ch growth spill_base lbl_ctr pred bb ps.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    LENGTH (cfg_preds_of cfg bb.bb_label) <> 1 /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred bb.bb_label ps ==>
    ?pre. ps.ps_stack = pre ++ MAP Var (input_vars_from pred bb.bb_instructions
                                         (live_vars_at liveness bb.bb_label 0)) /\
          EVERY (\op. op = dead_stack_marker) pre
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

The comment above the theorem in the script sketches why it holds.

## Completion Criteria

1. `lineage_entry_join_stack` has a proof with no `cheat` in its source, and the build below passes.
2. Every helper lemma lives in `venom/codegen/proofs/fnPlanLineageJoinScript.sml` (you may change its `Ancestors` line). No new cheats anywhere. The admitted lemmas this task may rely on are `fnLineageInv$lineage_entry_inventory` (admitted on purpose: a separate piece proves it) and admitted lemmas already in ancestor theories.
3. No duplicate lemmas: search for an existing one before adding a helper.
4. Each proof under ~50 lines; no proof step over the default 2.5 s tactic timeout.

**If the theorem is false as stated:** give a concrete counterexample scenario (which definitions make it fail) and the tightest sufficient fix. Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build fnPlanLineageJoinTheory
```
(run from the project root, the directory containing this task file and `holproject.toml`)

## Background

vyper-hol proves the Venom IR -> EVM assembly code generator correct. The DFS function planner plans each block once; at run time a join block (not exactly one predecessor) is entered from any predecessor, with the planner state that predecessor's code leaves (`lineage_entry`). Every predecessor of a join ends in a JMP (`block_entries_ready`), whose plan reorders the stack so it ends in the join's live-in variables (`join_target_ops`; `generate_inst_plan` returns NONE unless `join_reached`). This lemma says nothing but dead markers remains below them. Note `lineage_entry` takes the predecessor's plan run with arbitrary cleanup fields from a lineage state of pred, and the planner state of pred's run is otherwise its DFS state. Pred's block needs no premise of its own: lineage_entry gives its lookup and plan; the CFG gives that the join is a successor of pred.

## Domain Constraints

- Don't touch `semantics/`, `frontend/`, `lowering/`, `venom/defs/`, `venom/compiler/`, `venom/passes/`, `venom/codegen/defs/`, `venom/analysis/`. Edit only the files named in Completion Criteria 2. If a needed lemma is `[local]` elsewhere (e.g. `removeUnusedProofs$dominates_path_no_revisit`, `ssa_form_position`), re-derive what you need in your helper theory from exported results.
- Don't change any other frozen statement: `fnLineageInv$lineage_entry_inventory`, `fnLiveDefDom$live_def_dominates`, `fnPlanLineageJoin$lineage_entry_join_stack`, `fnLineageStatic$lineage_state_static` are each frozen.
- Don't raise or disable the tactic timeout; no `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>-`, `>~`, `>|`.
- A step timeout in a theory you haven't edited is box load: rebuild once, don't repair it.
- Keep probes inside your helper theory; remove them before finishing.
- Use `rename1`/`qpat_x_assum`, never generated names (`h'`, `x''`). Constants named `cp`/`base` exist, so `gen_tac` primes those variables; rename them.
- Commits: commit only the scripts you edit (never `.alan/`, `PLAN_*`, `STATE_*`, `LOG_*`, `LEARNINGS_*`, `DOSSIER_*`, this task file or tool outputs). End every commit message with these two lines:
  `Bot: opus (Claude Opus 5.5)` and `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Lineage states | venom/codegen/proofs/fnPlanLineageScript.sml | `dfs_aux_call`, `dfs_block_state_def`, `lineage_state` (rules, `_ind`, `_cases`), `lineage_entry_def`, `lineage_state_dfs_fields`, `lineage_entry_lineage_state` |
| Lineage inventory (admitted) | venom/codegen/proofs/fnLineageInvScript.sml | `lineage_entry_inventory`: a lineage entry state is wf_marked, and its non-marker stack slots and spills are variables live at the end of pred, and every such variable is on the stack or spilled |
| Live def dominance | venom/codegen/proofs/fnLiveDefDomScript.sml | `live_def_dominates` |
| Join entry stack | venom/codegen/proofs/fnPlanLineageJoinScript.sml | `lineage_entry_join_stack` |
| Lineage static facts | venom/codegen/proofs/fnLineageStaticScript.sml | `lineage_state_static` |
| Prefix planner | venom/codegen/proofs/fnPlanPrefixScript.sml | `generated_plan_state_wf_marked_def`, `generated_plan_state_wf_marked_wf` |
| Generated state wf | venom/codegen/proofs/genBlockSimScript.sml | `generated_plan_state_wf_def`, `plan_slots_bounded` |
| Planner | venom/codegen/defs/stackPlanGenScript.sml | `generate_inst_plan_def` (JMP fails unless `join_reached`), `join_target_ops_def`, `join_reached_def`, `generate_regular_inst_plan_def`, `generate_block_insts_plan_def`, `generate_block_plan_def`, `clean_stack_plan_def`, `prepare_params_plan_def`, `block_entries_ready_def`, `phi_block_ready_def`, `phi_uses_disjoint_def`, `phi_operands_ready_def`, `codegen_ready_fn_def`, `codegen_ready_inst_def`, `dead_stack_marker_def`, `non_param_insts_def`, `init_cleanup_plan_state_def`, `generate_fn_plan_aux_def` |
| Stack model / ops | venom/codegen/defs/ (stackModelScript.sml, stackPlanOpsScript.sml, stackPlanTypesScript.sml) | stack primitives, `release_dead_spills`, `restore_spilled_plan`, `reorder_plan` |
| Liveness defs | venom/analysis/liveness/defs/livenessDefsScript.sml | `live_vars_at_def`, `input_vars_from_def`, `build_phi_maps_def`, `liveness_analyze_def` |
| Liveness API | venom/analysis/liveness/proofs/livenessProofsScript.sml | `liveness_sound_proof` (witness via `cfg_exec_path`, which may leave a block early), `live_vars_at_transfer`, `live_vars_at_uses`, `live_vars_at_propagate(_range)`, `input_vars_from_non_phi`, `live_vars_at_cross_block`, `not_live_forward_in_block`, `not_live_cross_block`, `live_vars_at_forward_or_used`, `collect_phis_mem` |
| Liveness fixpoint | venom/analysis/liveness/proofs/livenessConvergenceProofsScript.sml | `liveness_recompute_convergence`, `liveness_recompute_edge_subset` (live-out is the union over successors of `input_vars_from`) |
| Other liveness proofs | venom/analysis/liveness/proofs/ (Block, Rank, Transfer, Invariant, Sound) | block transfer, rank / well-foundedness, PHI transfer |
| CFG analysis | venom/analysis/cfg/cfgAnalysisPropsScript.sml | `cfg_analyze_preserves_bb_succs`, preds/succs, reachable sets |
| CFG <-> fn edges | venom/codegen/defs/codegenReadyComputeScript.sml | `fn_cfg_edge_cfg_analyze`, `fn_reachable_cfg_analyze` |
| SSA, dominance | venom/defs/venomWfScript.sml | `fn_dominates_def`, `def_available_at_def`, `def_dominates_uses_def`, `phi_edge_uses_wf_def`, `fn_reachable_def`, `is_fn_path_def`, `ssa_form`, `wf_function` |
| Dominator analysis | venom/analysis/dominators/dominatorAnalysisPropsScript.sml | `dominates_trans`, `dominates_antisym`, `dominates_reachable` (for the analysed dominator relation; relate to `fn_dominates` or prove what you need on `fn_dominates` directly) |
| Dominance path lemmas (examples) | venom/passes/remove_unused/proofs/removeUnusedProofsScript.sml | `dominates_path_no_revisit` ([local]: re-derive) and nearby path lemmas |
| DFG | venom/analysis/dfg/dfgAnalysisPropsScript.sml, venom/analysis/dfg/defs/dfgDefsScript.sml | `dfg_build_function_defs_complete`, `normalize_operand_def` |
