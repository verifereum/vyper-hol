# TASK: ConcretizeMemLoc stage keeps the structural shape

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/passes/concretize_mem_loc/contract/

## Theorem Statement (FROZEN)

In `venom/passes/concretize_mem_loc/contract/concretizeStageShapeScript.sml`:

```sml
Theorem concretize_stage_shape:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\
  reserved_intervals_wf C.ctx_global_reserved /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  fmp_free_ctx C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  callee_first names C.ctx_functions ==>
  fmp_free_ctx C' /\ EVERY make_ssa_input_ok C'.ctx_functions /\
  callee_first names C'.ctx_functions /\
  ?eom. max_live_eom C' = SOME eom
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build concretizeStageShapeTheory` passes, with no CHEAT in the theory's build log and no `cheat` in any file you add or change.
2. No duplicate or near-duplicate lemmas: search the tree before adding one, and reuse what exists.

**If the theorem is false as stated:** give a concrete counterexample and the tightest sufficient fix. Do NOT weaken or change the statement.

## Build

```
holbuild -j4 build concretizeStageShapeTheory
```

Run from the project root (the directory with `holproject.toml`, where this file is).

## Background

vyper-hol proves the Vyper compiler correct. Its O1 Venom pipeline runs a walk of per-function passes; `ctx_pass_stage` relates a context `C` to `C'` where each function went through one pass step, here ConcretizeMemLoc. ConcretizeMemLoc computes a static memory layout for each function and rewrites each `ALLOCA` into an `ASSIGN` of the literal address, then removes NOPs. This theorem says the stage keeps the structural invariants later passes rely on (FMP-free functions, MakeSSA's input conditions, the callee-first order) and that the output context has a defined live end of memory (`max_live_eom`). The intuition is in the SML comment above the theorem.

## Domain Constraints

- New helper lemmas go in `concretizeStageShapeScript.sml` itself or in new theories under `venom/passes/concretize_mem_loc/` (e.g. `venom/passes/concretize_mem_loc/proofs/`). Do not edit any other existing theory, definition or statement.
- Never raise the tactic timeout; a step that runs over is a proof bug: split it.
- No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`.
- No `let` in theorem statements. Theories go in `Ancestors`, never `Libs`.
- Follow `AGENTS.md` at the project root.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Target script | `venom/passes/concretize_mem_loc/contract/concretizeStageShapeScript.sml` | the theorem, with intuition comments |
| Stage and shape defs | `venom/compiler/o1PassContractScript.sml` | `ctx_pass_stage`, `fn_pass_step`, `o1_ctx_shape`, `o1_fn_shape`, `fmp_free_ctx`, `callee_first`, `make_ssa_input_ok`, `o1_walk_view`, `make_ssa_input_ok_fmp_signature` |
| Pass dispatcher | `venom/defs/venomPassDispatcherScript.sml`, `venom/defs/venomPassScheduleScript.sml` | `execute_configured_fn_pass`, `fn_pass_effects_hold` and the per-tag effect tables, `introduces_no_invoke_edges`, `fn_pass_tag` |
| ConcretizeMemLoc defs | `venom/passes/concretize_mem_loc/defs/concretizeMemLocDefsScript.sml` | `concretize_function_fuel_in_context`, `apply_context_concretize_layout`, `apply_concretize_layout`, `concretize_function_with_positions`, `concretize_inst_with_positions`, `compute_function_layout_fuel_in_context`, `compute_function_layout_eval` |
| Layout defs | `venom/passes/concretize_mem_loc/defs/staticLayoutDefsScript.sml`, `staticLayoutWfScript.sml` | `mk_concretize_layout`, `allocation_eom_fold`, `allocation_end`, `global_reserved_end`, `reserved_intervals_wf`, `concretize_layout_wf` |
| Existing ConcretizeMemLoc lemmas | `venom/passes/concretize_mem_loc/proofs/` | esp. `concretizeMemLocTransitionProofsScript.sml` (metadata transition, sets_eom, invoke targets, layout certificates), `staticLayoutFoldProofsScript.sml` (`allocation_eom_fold_success`, `global_reserved_end_success`) |
| Shared pass defs | `venom/passes/shared/defs/passSharedDefsScript.sml`, `venom/simulation/defs/passSimulationDefsScript.sml` | `clear_nops_function`, `clear_nops_block`, `mk_assign_inst`, `mk_nop_inst`, `function_map_transform`, `block_map_transform` |
| WF / CFG defs | `venom/defs/venomWfScript.sml`, `venom/defs/cfgWfScript.sml` | `inst_wf`, `fn_inst_wf`, `bb_well_formed`, `wf_function`, `fn_cfg_edge`, `fn_reachable`, `is_fn_path`, `def_on_all_paths`, `fn_defs_reach_uses`, `fn_phi_*`, `all_reachable` |
| Instruction defs | `venom/defs/venomInstScript.sml` | `bb_succs`, `fn_insts`, `no_raw_fmp_ops`, `fn_fmp_convention_eq`, `is_raw_fmp_opcode` |
| max_live_eom | `venom/codegen/defs/stackPlanGenScript.sml` | `max_live_eom`, `collect_fn_eoms` |
| Similar stage proofs | `venom/compiler/o1ContractLowerDloadStageScript.sml`, `venom/compiler/o1ContractFmpLoweringScript.sml`, `venom/compiler/o1ComposeSupportScript.sml` | how other stages prove `fmp_free_ctx`, `callee_first`, `max_live_eom` (`ctx_pass_stage_max_live_eom`, `collect_fn_eoms_rel`) |
| Invoke targets | `venom/defs/venomFnScheduleRunnerScript.sml` | `fn_invoke_targets` |

## Notes

The statement was checked against the definitions by reading them; it has been parsed and type-checked by a build.
