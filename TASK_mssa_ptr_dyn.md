# TASK: MakeSSA pointer discipline: the lockstep rows and revert positions

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/compiler/ (o1ContractMakeSsaPtrRowsScript.sml, o1ContractMakeSsaPtrPosScript.sml)

## Theorem Statement (FROZEN)

The piece, already proved in `venom/compiler/o1ContractMakeSsaPtrScript.sml` from the helpers below:

```sml
Theorem make_ssa_stage_ptr:
  !rpolicy D view C C' vs names lo.
    ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ EVERY make_ssa_input_ok C.ctx_functions /\
    callee_first names C.ctx_functions /\
    fixed_region_reserved lo C /\ ptr_discipline lo C vs ==>
    ptr_discipline lo C' vs
```

Prove these helpers, each stated with `cheat` (weakly frozen: change one only if it is false, and say so with a counterexample):
- `o1ContractMakeSsaPtrRows`: `lockstep_ptr_rows`, `make_ssa_current_fn_dalloca`
- `o1ContractMakeSsaPtrPos`: `make_ssa_current_fn_block_last`, `make_ssa_pos_revert`, `make_ssa_lockstep_revert`

**Do not modify the frozen statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build o1ContractMakeSsaPtrTheory` passes at the default tactic timeout.
2. The five helpers above are proved without a cheat.
3. The frozen statement is unchanged, byte for byte.
4. No duplicate or near-duplicate lemmas; search before adding a helper.

**If a helper is false as stated:** produce a counterexample, state the tightest fix, and stop. Do NOT weaken the frozen statement.

## Build

```
holbuild -j4 build o1ContractMakeSsaPtrTheory
```

## Background

Part of vyper-hol's O1 pipeline proof: MakeSSA keeps the pointer discipline `ptr_discipline`. Its per-state rows (access_ok, taint_ok, allocas) carry across the frame lockstep between MakeSSA's output and input (o1FrameLockstep); the helpers are the per-instruction transfer and the static facts about where REVERTs land. The comments above each helper say why it should hold.

## Domain Constraints

- Put helper lemmas in `o1ContractMakeSsaPtrRowsScript.sml` / `o1ContractMakeSsaPtrPosScript.sml`, or new theories next to them in `venom/compiler/`. Do not edit any other existing file, and do not edit `o1ContractMakeSsaPtrOkScript.sml` (another job proves it).
- Admitted (cheated) by other jobs, use their statements as given and don't prove or edit them: `make_ssa_current_fn_origin`, `make_ssa_current_fn_frame_lockstep`, `make_ssa_current_fn_revert_forward_at`, `make_ssa_current_fn_wf_ssa`, `make_ssa_current_fn_phis_non_degenerate`, `make_ssa_current_fn_ptr_ok`.
- `make_ssa_current_fn_block_last` may unfold `make_ssa_current_fn`; follow the stage-by-stage style of `makeSsaCurrentCfgScript.sml` (block_succs_map preserved by each stage).
- No `cheat`, no new axioms, no raised tactic timeout, no `TRY`/`ORELSE` around `metis_tac` or other search: select goals with `>-`, `>~`, `>|`.
- Proofs at most ~50 lines each; split into helper lemmas. Use `rename1`, never generated names.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Targets | venom/compiler/o1ContractMakeSsaPtrRowsScript.sml, o1ContractMakeSsaPtrPosScript.sml | the helpers |
| Consumer | venom/compiler/o1ContractMakeSsaPtrScript.sml | make_ssa_stage_ptr's proof, which uses them |
| Lockstep | venom/compiler/o1FrameLockstepScript.sml | lockstep_sim, inst_pair, op_rename, state_rel, ghost_rel; lockstep_rel, inst_pair_ops, inst_pair_ops_ghost, write_ranges_pair, read_ranges_pair, read_ranges_other, inst_mem_ranges_pair, execution_frame_fields, op_rename_ghost |
| Pointer discipline | venom/compiler/ptrDisciplineScript.sml | access_ok, taint_ok, about_to_revert, op_prov, op_taint |
| Codegen relations | venom/codegen/defs/contextCodegenRelScript.sml, venom/codegen/defs/codegenRelScript.sml | active_inst, in_revert_forward, revert_forward_at, revert_forward_pair, source_memory_write_ranges, source_memory_read_ranges |
| MakeSSA lockstep (admitted) | venom/passes/make_ssa/proofs/makeSsaCurrentLockstepScript.sml | make_ssa_pos, make_ssa_current_fn_frame_lockstep |
| Revert forward (admitted) | venom/passes/make_ssa/proofs/makeSsaCurrentRevertForwardScript.sml | make_ssa_current_fn_revert_forward_at |
| Origin (admitted) | venom/passes/make_ssa/proofs/makeSsaCurrentOriginScript.sml | make_ssa_current_fn_origin |
| MakeSSA defs | venom/passes/make_ssa/defs/makeSsaCurrentDefsScript.sml | make_ssa_current_fn and its stages |
| MakeSSA facts | venom/passes/make_ssa/proofs/makeSsaCurrentPropsScript.sml, makeSsaCurrentCfgScript.sml | make_ssa_current_fn_labels, block_succs_map stage lemmas, rename_current_inst lemmas |
| Well-formedness | venom/defs/venomWfScript.sml | wf_function, bb_well_formed |
| Instructions | venom/defs/venomInstScript.sml | is_terminator, mem_write_ops/mem_read_ops (grep venom/) |

## Notes

Paths are relative to the project root (the directory of this file).
