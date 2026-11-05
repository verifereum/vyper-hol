# TASK: The entry block's parameter prefix, with Inv, labels and alias facts after it

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/codegen/proofs/ (theorem in fnEntryParamsScript.sml)

## Theorem Statement (FROZEN)

In `venom/codegen/proofs/fnEntryParamsScript.sml`:

```sml
Theorem entry_prefix_frame_sim:
  !fuel ctx cp lo o2pc prog liveness dfg fn ch growth spill_base lbl_ctr ps0
   param_ops ps1 r vs as ra rest Inv.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    codegen_ready_fn fn /\ retpc_shape_ok fn /\ opaque_use_ok fn /\
    ps0 = init_cleanup_plan_state ch growth spill_base lbl_ctr /\
    prepare_params_plan liveness fn ps0 = (param_ops, ps1) /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= spill_base /\
    ps1.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    (!off. MEM (SOSpill off) param_ops ==> off < dimword (:256)) /\
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions) < dimword (:256) /\
    fn_entry_state_rel cp fn vs as ra rest /\
    fn_entry_inv Inv ctx fn vs /\ reachability_closed Inv ctx /\
    asm_block_at prog as.as_pc
      (execute_plan cp.cp_initial_fmp
         (SOLabel (HD fn.fn_blocks).bb_label :: param_ops))
    ==>
    ?n as' vs_p.
      asm_steps lo o2pc prog n as = AsmOK as' /\
      as'.as_pc = as.as_pc +
        LENGTH (execute_plan cp.cp_initial_fmp
                  (SOLabel (HD fn.fn_blocks).bb_label :: param_ops)) /\
      exec_block fuel ctx (HD fn.fn_blocks) (vs with vs_inst_idx := 0) =
        exec_block fuel ctx (HD fn.fn_blocks) vs_p /\
      vs_p.vs_inst_idx = LENGTH (get_params (HD fn.fn_blocks).bb_instructions) /\
      fn_frame_inv ctx cp lo fn ra rest as.as_memory ps1 vs_p as' /\
      vs_p.vs_current_bb = vs.vs_current_bb /\
      vs_p.vs_labels = vs.vs_labels /\
      vs_p.vs_call_ctx = vs.vs_call_ctx /\
      (!inst. active_inst fn inst vs_p ==> Inv ctx fn inst vs_p) /\
      (!at. MEM at ps1.ps_stack \/ at IN FDOM ps1.ps_spilled ==>
         operand_val (frame_view fn ra vs_p) lo at =
         operand_val (frame_view fn ra vs_p) lo (normalize_operand dfg [] at))
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build fnEntryParamsTheory` passes at the default tactic timeout, and `entry_prefix_frame_sim` is saved without a cheat.
2. The statement above is unchanged, byte for byte.
3. No duplicate or near-duplicate lemmas; search before adding a helper.

**If the theorem is false as stated:** produce a counterexample, state the tightest fix, and stop. Do NOT weaken the statement.

## Build

```
holbuild -j4 build fnEntryParamsTheory
```

## Background

Part of the codegen (Venom to assembly) correctness proof in vyper-hol: the fuel induction behind `venomToAsmProps$gen_fn_simulation`, whose entry-block step is `fnEntryStep$fn_entry_block_step`. This theorem is one of its route lemmas; the comment above the statement says why it should hold.

## Domain Constraints

- Put helper lemmas in `fnEntryParamsScript.sml` itself. Do not edit any other existing theory; in particular never touch `semantics/`, `frontend/`, `lowering/`, `venom/defs/`, `venom/compiler/`, `venom/passes/`, or any shared ancestor in `venom/codegen/`.
- No `cheat`, no new axioms, no raised tactic timeout, no `TRY`/`ORELSE` around `metis_tac` or other search: select goals with `>-`, `>~`, `>|`.
- Proofs at most ~50 lines each; split into helper lemmas. Use `rename1`, never generated names.
- entry_params_frame_sim (fnFrameBoundaryScript.sml) is proved but only gives an existential vs_p; its proof shows which state that is. Do not edit fnFrameBoundaryScript.sml or fnFrameBoundaryEntryParamsScript.sml; put helpers in fnEntryParamsScript.sml. entry_run_block in the same file is proved; leave it as is.

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
