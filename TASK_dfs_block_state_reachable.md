# TASK: Every reachable block is planned by the function DFS (dfs_block_state_reachable)

## Meta
Status: planned
Priority: P0
Created: 2026-11-04
Location: venom/codegen/proofs/fnPlanCoverScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

```sml
Theorem dfs_block_state_reachable:
  !liveness dfg cfg ch growth spill_base lbl_ctr fn fn_ops ps_end lbl bb.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
    fn_reachable fn lbl /\ lookup_block lbl fn.fn_blocks = SOME bb
    ==>
    ?ps_dfs block_ops ps_dfs_after pre post.
      dfs_block_state liveness dfg cfg fn
        (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps_dfs /\
      generate_block_plan liveness dfg cfg fn bb ps_dfs =
        SOME (block_ops, ps_dfs_after) /\
      fn_ops = pre ++ block_ops ++ post
```

The definitions it uses (`dfs_aux_call`, `dfs_succs_call`, `dfs_block_state`
in `venom/codegen/proofs/fnPlanLineageScript.sml`) are frozen too.

**Do not modify this statement or those definitions.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild --gcthreads 8 -j4 build fnPlanCoverTheory` passes with zero CHEAT warnings and zero failures in `fnPlanCoverTheory` and any helper theory you add.
2. No duplicate or near-duplicate lemmas: each helper exists once, in its most general form. Search the existing theories (below) before proving a fact.
3. New helper theories, if any, are registered in `holproject.toml` the way the existing ones are.

Scope: only `dfs_block_state_reachable`. `fnPlanLineageScript.sml` holds another
cheated theorem (`lineage_state_block_plan`) that a separate run is proving;
don't touch it or its file, and don't make fnPlanCover depend on it.

**If the theorem is false as stated:**
- Produce a HOL4 counterexample (concrete function, `EVAL`).
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
cd <this directory>
holbuild --gcthreads 8 -j4 build fnPlanCoverTheory
```

Always pass `--gcthreads 8` (a Poly/ML GC assertion fails without it on this host).

## Background

vyper-hol's Venom-to-EVM code generator plans each function with a DFS over
the CFG from the entry block (`generate_fn_plan_aux` / `generate_succs_plan`
in `venom/codegen/defs/stackPlanGenScript.sml`), planning each block once.
`dfs_block_state` (fnPlanLineage) is the planner state a block was planned
from, defined by rules (`dfs_aux_call`, `dfs_succs_call`) that follow the
planner's recursion call for call.

The block-level simulation needs, at each jump, that the target block was
planned: it has a DFS state, its block plan from that state succeeds, and
its code is a contiguous slice of the function's plan. This theorem says
that for every block reachable from the entry in the CFG (`fn_reachable`).
Notes on why it should hold are in the SML comment above the theorem.

## Domain Constraints

- holbuild only (no Holmake, no `holbuild run`/`repl`). Probe with scratch lemmas ending in `cheat` and rebuild.
- Never raise the tactic timeout (no `--tactic-timeout`, no holproject edits to it). A step that runs over 2.5 s must be split.
- No `TRY`/`ORELSE` around metis or other search.
- No `cheat` left anywhere you touched; no new axioms; no `let` in theorem statements.
- Do not edit definitions in `venom/codegen/defs`, `venom/analysis` or `fnPlanLineageScript.sml`.
- Keep helpers in `venom/codegen/proofs/` (in fnPlanCoverScript.sml or a new `fnPlanCover*Script.sml`).

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Planner | venom/codegen/defs/stackPlanGenScript.sml | `generate_fn_plan_with_cleanup_analyzed`, `generate_fn_plan_aux`, `generate_succs_plan`, `generate_block_plan`, `codegen_ready_fn` |
| DFS rules | venom/codegen/proofs/fnPlanLineageScript.sml | `dfs_aux_call`, `dfs_succs_call`, `dfs_block_state` and their rules/induction |
| Planner decomposition | venom/codegen/proofs/fnPlanDecompScript.sml | facts about the function planner's recursion (`fn_plan_aux_per_block` and others) |
| Earlier DFS helpers | venom/codegen/proofs/fnPlanLineageReplayScript.sml | lemmas about the DFS recursion proved by an earlier run |
| CFG | venom/analysis/cfg/defs/cfgDefsScript.sml, venom/analysis/cfg/cfgAnalysisPropsScript.sml, cfgHelpersScript.sml | `cfg_analyze`, `cfg_succs_of`, `bb_succs_in_cfg_succs` |
| Reachability | venom/defs/venomWfScript.sml and grep `fn_reachable` | `fn_reachable`, `wf_function` |

## Notes

- A statement check found it provable. It expects one routine invariant: the final visited set is closed under the successors of every planned block, and a label is only skipped as visited after it was planned.
