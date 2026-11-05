# TASK: LowerDload O1 contract — re-establish `lower_dload_stage_sim` on the current base

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/compiler/o1ContractLowerDloadSimScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem lower_dload_stage_sim:
  !rpolicy D view C C' vs names.
    ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
    dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
    o1_src_inv D C vs /\ callee_first names C.ctx_functions ==>
    ctx_sim D C C' vs vs
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build o1ContractLowerDloadSimTheory` passes with zero CHEAT warnings and zero FAILs, and the frozen statement above is unchanged byte for byte.
2. No duplicate or near-duplicate lemmas — each helper exists once in its most general form.
3. Edit only `venom/compiler/o1ContractLowerDloadSimScript.sml` and theories in `venom/compiler/` named `o1LowerDload*` (existing or new). Their definitions and lemma statements are yours to change. Do not edit any other theory: not `o1ContractLowerDload*` (other than the Sim file), `o1PassContract`, `ptrDiscipline`, `unitMemInv`, anything under `venom/defs`, `venom/passes`, `semantics/`, `lowering/`.

**If the theorem is false as stated:**
- Produce a concrete counterexample (program, initial state, which conjunct fails).
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build o1ContractLowerDloadSimTheory
```
Run from the project root (the directory with `holproject.toml`).

## Background

The input/output runs of the LowerDload pass match up to the dead bytes D (`ctx_sim`, `dead_result_rel`). This is one row of the pass's O1 contract.

LowerDload expands each `DLOAD off` into `ALLOCA 32; ADD [off; Label "code_end"]; CODECOPY; MLOAD`, and each `DLOADBYTES` into the ADD and a CODECOPY. So the output has one more 32-byte ALLOCA site per DLOAD, which moves the later alloca sites of a frame. The pointer discipline and taint conjuncts of `o1_src_inv` are what make the shifted addresses unobservable.

The theorem was fully proved on an older base of this repository (no cheats), with the proof spread over the `o1LowerDload*` leaf theories now in `venom/compiler/` and the lemmas in `o1ContractLowerDloadSimScript.sml`. Those files were copied onto the current base unchanged, apart from one port: a new leaf `o1LowerDloadPtrDisciplineScript.sml` (`ptr_discipline_fn_ptr_ok`) restores the old shape of `ptr_discipline`, whose function conjunct is now `fn_ptr_ok P fn /\ fn_ptr_ok P (reachable_fn fn)`. The job is to repair the proofs that the base's semantic and contract changes broke.

## Domain Constraints

- HOL4 via holbuild only. No Holmake, no `holbuild run`/`repl`.
- Never raise or disable the tactic timeout (2.5 s per step). A slow step is a proof bug: split it.
- No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`.
- No axioms, no cheats. Prefer existing definitions to new ones.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Frozen theorem and its top-level lemmas | `venom/compiler/o1ContractLowerDloadSimScript.sml` | runner induction, root entry, `ld_runner_simulation` |
| Proof leaves | `venom/compiler/o1LowerDload*Script.sml` | joint relation (`o1LowerDloadJointRelation`), shared-state agreement (`o1LowerDloadShared`, `ld_shared_agree`), per-opcode steps (`o1LowerDloadJoint*`), dispatch (`o1LowerDloadOrdinaryDispatch`) |
| The pass | `venom/passes/lower_dload/defs/lowerDloadDefsScript.sml` | `lower_dload_inst_supply`, `lower_dload_function_supply` |
| Pass facts | `venom/compiler/o1ContractLowerDloadScript.sml` | member/control/labels/shape lemmas; `opaque_use_ok`, `gas_var`, `gas_use_ok` usage |
| Contract defs | `venom/compiler/o1PassContractScript.sml` | `ctx_sim`, `o1_src_inv`, `o1_run_state_ok`, `ctx_pass_stage`, `o1_ctx_shape`, `opaque_use_ok`, `gas_variant` |
| Pointer discipline, taint, dead bytes | `venom/compiler/ptrDisciplineScript.sml` | `ptr_discipline`, `fn_ptr_ok`, `access_ok`, `taint_ok`, `frame_reachable`, `dead_result_rel` |
| Semantics | `venom/defs/venomExecSemanticsScript.sml`, `venom/defs/venomStateScript.sml` | `exec_gas` (pops `vs_gas_readings`), `exec_read0`, `merge_callee_state` (propagates `vs_gas_readings`), `setup_callee`, `run_context` |

## Notes

Changes on the current base that the copied proof predates:
- GAS no longer goes through `exec_read0`: `exec_gas` pops the next element of `vs_gas_readings` (an empty list reads 0w), and `merge_callee_state` carries the callee's remaining readings back to the caller. The copied joint relation (`ld_joint_local_fields`, `ld_shared_agree`) does not mention `vs_gas_readings`, and `ld_joint_read0_step` lists GAS among the read0 opcodes; that is where the first build fails. Both runs of `ctx_sim D C C' vs vs` start from the same state.
- `opaque_use_ok` now includes the GAS-variable condition (`gas_var`/`gas_use_ok`).
- `ptr_discipline` carries `lo <= vs.vs_alloca_next` and `fn_ptr_ok` of `reachable_fn fn` (handled by the new leaf, see Background).
- Other contract changes since the old base (static call frames, MakeSSA input rows) may surface further down the build.

The first build on this base built about 40 leaves and stopped at `o1LowerDloadJointRead0Theory` (`ld_joint_read0_step`, the GAS case).
