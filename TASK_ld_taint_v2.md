# TASK: LowerDload O1 contract — `lower_dload_stage_taint`

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Rebased: 2026-11-05 onto the current branch head
Location: venom/compiler/o1ContractLowerDloadTaintScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem lower_dload_stage_taint:
  !rpolicy D view C C' vs names.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ callee_first names C.ctx_functions ==>
    taint_within D C' vs
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build o1ContractLowerDloadTaintTheory` passes with zero CHEAT warnings and zero FAILs, and the frozen statement above is unchanged byte for byte.
2. No duplicate or near-duplicate lemmas — each helper exists once in its most general form. New helper theories are fine; put them under `venom/compiler/` named `lowerDload*`.
3. Do not edit any definition, any other theorem's statement, or any theory outside the ones you create plus `o1ContractLowerDloadTaintScript.sml` and the task-created `venom/compiler/lowerDload*Script.sml` leaves. `o1ContractLowerDloadScript.sml` and every other shared theory are read-only; put new helpers in `lowerDload*` leaf theories next to the target. The `venom/compiler/o1LowerDload*Script.sml` theories (another proof's leaves) may only gain new lemmas, never changed ones.

**If the theorem is false as stated:**
- Produce a concrete counterexample (program, initial state, which conjunct fails).
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build o1ContractLowerDloadTaintTheory
```
Run from the project root (the directory with `holproject.toml`).

## Background

The LowerDload output's tainted (unwritten or leftover) memory reaches only the dead bytes D (`taint_within`). This is one row of the pass's O1 contract; the contract theorem `o1_contract_lower_dload` in `venom/compiler/o1ContractLowerDloadStageScript.sml` uses it.

LowerDload expands each `DLOAD off` into `ALLOCA 32; ADD [off; Label "code_end"]; CODECOPY; MLOAD`, and each `DLOADBYTES` into the ADD and a CODECOPY. So the output has one more 32-byte ALLOCA site per DLOAD, which moves the later alloca sites of a frame. The pointer discipline and taint conjuncts of `o1_src_inv` are what make the shifted addresses unobservable.

## Domain Constraints

- HOL4 via holbuild only. No Holmake, no `holbuild run`/`repl`.
- Never raise or disable the tactic timeout (2.5 s per step). A slow step is a proof bug: split it.
- No `TRY`/`ORELSE` around `metis_tac` or other search.
- No new definitions unless unavoidable; prefer existing ones. No axioms, no cheats.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| The pass | `venom/passes/lower_dload/defs/lowerDloadDefsScript.sml` | `lower_dload_inst_supply`, `lower_dload_function_supply`, `dload_offset_ok`, `ctx_dload_count`, `dload_headroom_ok` |
| Pass facts | `venom/compiler/o1ContractLowerDloadScript.sml` | member/control/labels/shape lemmas about `lower_dload_function_supply` |
| Stage helpers | `venom/compiler/o1ContractLowerDloadStageScript.sml` | `lower_dload_stage_fn`, `lower_dload_stage_lookup`, no-DLOAD-after facts (local; copy into your theory or make non-local only if needed) |
| Task-created leaves | `venom/compiler/lowerDload*Script.sml` | this task's earlier accepted results, ported to the current base; `lowerDloadSupplySegmentScript.sml` holds the supply append/segment/position lemmas formerly added to `o1ContractLowerDloadScript.sml` |
| Stage simulation leaves | `venom/compiler/o1LowerDload*Script.sml` | the proof of the sibling row `lower_dload_stage_sim` (joint relocation relation, shared state, occurrence, call/return boundaries); reuse their lemmas rather than duplicating them |
| Contract defs | `venom/compiler/o1PassContractScript.sml` | `ctx_sim`, `o1_src_inv`, `o1_run_state_ok`, `ctx_pass_stage`, `o1_ctx_shape`, `callee_first`, `fmp_free_ctx` |
| Pointer discipline, taint, dead bytes | `venom/compiler/ptrDisciplineScript.sml` | `ptr_discipline`, `fn_ptr_ok`, `ptr_use_ok`, `access_ok`, `taint_ok`, `allocas_from`, `taint_within`, `dead_result_rel`, `dead_wf` and their lemmas |
| Raw memory invariant | `venom/compiler/unitMemInvScript.sml`, `venom/compiler/memSafeRunScript.sml`, `venom/compiler/unitTransformDefsScript.sml` | `mem_inv`, `raw_mem_ok`, `mem_inv_mono`, `o1_initial_state_ok`, frontier lemmas |
| Semantics | `venom/defs/venomExecSemanticsScript.sml` | `exec_alloca` (per-frame, lazy, idempotent per inst_id), `merge_callee_state` (INVOKE restores the caller's frontier), DLOAD/DLOADBYTES/CODECOPY/MLOAD steps, `run_context` |
| Memory locations | `venom/analysis/shared/defs/memLocDefsScript.sml` | read/write ranges per opcode |
| State relations | `venom/defs/stateEquivScript.sml`, `venom/simulation/defs/passSimulationDefsScript.sml` | state equivalences and pass-simulation framework |
| Other stage contracts proved the same rows | `venom/compiler/o1ContractFmpLoweringScript.sml`, `venom/compiler/o1DretDesugarContractScript.sml`, `venom/compiler/o1PassLiftScript.sml` | examples of discharging `ctx_sim` / `o1_src_inv` rows for other passes |

## Notes

`access_ok_def` (venom/compiler/ptrDisciplineScript.sml) now requires `0 < sz` for compared pointers, which excludes the zero-size-site witness (`ALLOCA 0; DLOAD 0; ALLOCA 0; EQ`); `ptr_discipline lo C vs` includes `lo <= vs.vs_alloca_next`.

An earlier run on this branch left proved helpers in `venom/compiler/o1ContractLowerDloadTaintScript.sml` (overwrite and local taint boundaries, data-copy taint, call-return allocation boundaries, dead-set transport, relational overwrite interface). Reuse them; the main theorem is still open.

The statement was checked by reading the definitions; it is believed true, not proven.

The task was moved to a newer base on 2026-11-05. Since the previous base: GAS reads `vs_gas_readings` (`exec_gas` pops it; `opaque_use_ok` gained `gas_var`/`gas_use_ok`); SSTORE/TSTORE and other state writes fail in static call frames (`cc_static`), so `ld_storage_observation_backward` gained a `cc_static` equality premise; the legacy `lowerDloadClassify`/`lowerDloadProofs`/`lowerDloadSim` theories and the legacy `ld_fresh_vars`/`ld_no_original_alloca` definitions were deleted. All task-created leaves build at this base with no cheat.
