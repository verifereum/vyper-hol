# TASK: A function run ending in IntRet keeps five immutable state fields

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/codegen/proofs/ (theorem in fnRunFieldsScript.sml)

## Theorem Statement (FROZEN)

In `venom/codegen/proofs/fnRunFieldsScript.sml`:

```sml
Theorem run_blocks_intret_fields:
  !fuel ctx fn vs ret vs'.
    run_blocks fuel ctx fn vs = IntRet ret vs' ==>
    vs'.vs_call_ctx = vs.vs_call_ctx /\ vs'.vs_tx_ctx = vs.vs_tx_ctx /\
    vs'.vs_block_ctx = vs.vs_block_ctx /\ vs'.vs_code = vs.vs_code /\
    vs'.vs_prev_hashes = vs.vs_prev_hashes
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build fnRunFieldsTheory` passes at the default tactic timeout, and `run_blocks_intret_fields` is saved without a cheat.
2. The statement above is unchanged, byte for byte.
3. No duplicate or near-duplicate lemmas; search before adding a helper.

**If the theorem is false as stated:** produce a counterexample, state the tightest fix, and stop. Do NOT weaken the statement.

## Build

```
holbuild -j4 build fnRunFieldsTheory
```

## Background

Part of the codegen (Venom to assembly) correctness proof in vyper-hol: the fuel induction behind `venomToAsmProps$gen_fn_simulation`, whose entry-block step is `fnEntryStep$fn_entry_block_step`. This theorem is one of its route lemmas; the comment above the statement says why it should hold.

## Domain Constraints

- Put helper lemmas in `fnRunFieldsScript.sml` itself. Do not edit any other existing theory; in particular never touch `semantics/`, `frontend/`, `lowering/`, `venom/defs/`, `venom/compiler/`, `venom/passes/`, or any shared ancestor in `venom/codegen/`.
- No `cheat`, no new axioms, no raised tactic timeout, no `TRY`/`ORELSE` around `metis_tac` or other search: select goals with `>-`, `>~`, `>|`.
- Proofs at most ~50 lines each; split into helper lemmas. Use `rename1`, never generated names.
- passes/memmerging/proofs/mmBlockSimProofsScript.sml has [local] call_ctx-only versions at run_block level; they are not usable from here and that directory must not be edited.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Target theories | venom/codegen/proofs/fnEntry*Script.sml, fnRunFieldsScript.sml, fnEntryStepScript.sml | entry-step lemmas and the piece |
| Spec | venom/codegen/proofs/fnSimSpecScript.sml | gen_fn_sim_at, gen_fn_frame_sim_at |
| Block body | venom/codegen/proofs/fnBlockBodyScript.sml | block_rest, block_plan_state, block_body_frame_sim (admitted) |
| Frame relation | venom/codegen/defs/frameRelScript.sml | fn_frame_inv, fn_entry_state_rel, fn_return_state_rel, shared_state_rel |
| Entry params | venom/codegen/proofs/fnFrameBoundaryScript.sml, fnFrameBoundaryEntryParamsScript.sml | entry_params_frame_sim and its helpers |
| Planner | venom/codegen/defs/stackPlanGenScript.sml | generate_context_plan, generate_fn_plan_with_cleanup_analyzed, generate_fn_plan_aux, generate_block_plan, prepare_params_plan, codegen_ready_fn, block_entries_ready |
| Planner lineage | venom/codegen/proofs/fnPlanLineageScript.sml | dfs_aux_call, dfs_block_state, lineage_state |
| Placement | venom/codegen/proofs/fnPlanPlaceScript.sml, fnPlanPlaceFnRegionScript.sml, fnPlanPlaceDfsBlockScript.sml, fnPlanPlaceRevertPostambleScript.sml | fn_region_placed, labelled_asm_slice_placed, codegen_region_slice, provenance lemmas |
| Plan decomposition | venom/codegen/proofs/fnPlanDecompScript.sml | ops_contain_at, asm_block_at_from_contain |
| Allocator monotonicity | venom/codegen/proofs/allocMonoScript.sml | *_next_offset, fn_plan_aux_alloc_mono |
| Spill bounds | venom/codegen/proofs/planSpillBoundsScript.sml, contextPlanLayoutPropsScript.sml | generate_context_plan_access_bounded, generate_context_plan_spill_gap |
| asm steps | venom/codegen/proofs/blockSimHelpersScript.sml, stackOpSimScript.sml | asm_steps_compose_ok/_halt/_revert/_fault, asm_steps_add |
| Codegen relations | venom/codegen/defs/contextCodegenRelScript.sml | active_inst, enters_block, fn_entry_inv, reachability_closed, codegen_context_obligations |
| Venom semantics | venom/defs/venomExecSemanticsScript.sml, venom/props/venomExecPropsScript.sml, venom/props/venomInstPropsScript.sml | step_inst, exec_block, run_blocks, run_blocks_unfold, run_block_def, step_preserves_* |
| Unit shape | venom/compiler/unitShapeDefsScript.sml | unit_shape_ok, fn_shape_ok |
| Consumer | venom/codegen/venomToAsmPropsScript.sml | the fuel induction that uses the piece |

## Notes

Paths are relative to the project root (the directory of this file).
