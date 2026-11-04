# TASK: LowerDload O1 contract — `lower_dload_stage_mem`

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: venom/compiler/o1ContractLowerDloadMemScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem lower_dload_stage_mem:
  !rpolicy D view C C' vs names.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ callee_first names C.ctx_functions ==>
    mem_inv raw_mem_ok C' vs
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build o1ContractLowerDloadMemTheory` passes with zero CHEAT warnings and zero FAILs, and the frozen statement above is unchanged byte for byte.
2. No duplicate or near-duplicate lemmas — each helper exists once in its most general form. New helper theories are fine; put them under `venom/compiler/` or `venom/passes/lower_dload/proofs/`.
3. Do not edit any definition, any other theorem's statement, or any theory outside the ones you create plus `o1ContractLowerDloadMemScript.sml` (adding helper lemmas to `o1ContractLowerDloadScript.sml` is fine).

**If the theorem is false as stated:**
- Produce a concrete counterexample (program, initial state, which conjunct fails).
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build o1ContractLowerDloadMemTheory
```
Run from the project root (the directory with `holproject.toml`).

## Background

The LowerDload output keeps raw memory safety (`mem_inv raw_mem_ok`) on all reachable states. This is one row of the pass's O1 contract; the contract theorem `o1_contract_lower_dload` in `venom/compiler/o1ContractLowerDloadStageScript.sml` uses it.

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
| Old function-level sim | `venom/passes/lower_dload/proofs/lowerDloadSimScript.sml`, `venom/passes/lower_dload/lowerDloadCorrectnessScript.sml` | block/instruction-level simulation lemmas for the expansion (under a no-memory-read assumption) |
| Contract defs | `venom/compiler/o1PassContractScript.sml` | `ctx_sim`, `o1_src_inv`, `o1_run_state_ok`, `ctx_pass_stage`, `o1_ctx_shape`, `callee_first`, `fmp_free_ctx` |
| Pointer discipline, taint, dead bytes | `venom/compiler/ptrDisciplineScript.sml` | `ptr_discipline`, `fn_ptr_ok`, `ptr_use_ok`, `access_ok`, `taint_ok`, `allocas_from`, `taint_within`, `dead_result_rel`, `dead_wf` and their lemmas |
| Raw memory invariant | `venom/compiler/unitMemInvScript.sml`, `venom/compiler/memSafeRunScript.sml`, `venom/compiler/unitTransformDefsScript.sml` | `mem_inv`, `raw_mem_ok`, `mem_inv_mono`, `o1_initial_state_ok`, frontier lemmas |
| Semantics | `venom/defs/venomExecSemanticsScript.sml` | `exec_alloca` (per-frame, lazy, idempotent per inst_id), `merge_callee_state` (INVOKE restores the caller's frontier), DLOAD/DLOADBYTES/CODECOPY/MLOAD steps, `run_context` |
| Memory locations | `venom/analysis/shared/defs/memLocDefsScript.sml` | read/write ranges per opcode |
| State relations | `venom/defs/stateEquivScript.sml`, `venom/simulation/defs/passSimulationDefsScript.sml` | state equivalences and pass-simulation framework |
| Other stage contracts proved the same rows | `venom/compiler/o1ContractFmpLoweringScript.sml`, `venom/compiler/o1DretDesugarContractScript.sml`, `venom/compiler/o1PassLiftScript.sml` | examples of discharging `ctx_sim` / `o1_src_inv` rows for other passes |

## Notes

The statement was checked by reading the definitions; it is believed true, not proven.
