# TASK: ConcretizeMemLoc stage simulation and static memory bound

## Meta
Status: planned
Priority: P0
Created: 2026-11-02
Location: venom/passes/concretize_mem_loc/contract/

## Theorem Statement (FROZEN)

In `venom/passes/concretize_mem_loc/contract/concretizeStageSimScript.sml`:

```sml
Theorem concretize_stage_sim:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\
  mem_inv raw_mem_ok C vs /\ ptr_discipline C vs ==>
  ctx_sim C C' vs vs

Theorem concretize_stage_static_mem:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_initial_state_ok vs /\
  mem_inv raw_mem_ok C vs /\ ptr_discipline C vs /\
  ctx_eom_bounded eom C C' ==>
  mem_inv (static_mem_ok eom) C' vs
```

Supporting definitions: `ptr_discipline`, `frame_reachable`, `access_ok`,
`fn_ptr_ok` in `venom/compiler/ptrDisciplineScript.sml`; `ctx_pass_stage`,
`o1_walk_view`, `walk_view`, `fn_pass_step`, `fn_steps`, `ctx_sim`,
`o1_ctx_shape`, `ctx_eom_bounded` in `venom/compiler/o1PassContractScript.sml`;
`mem_inv`, `raw_mem_ok`, `static_mem_ok`, `inst_mem_ranges` in
`venom/compiler/unitMemInvScript.sml`; the pass in
`venom/passes/concretize_mem_loc/defs/concretizeMemLocDefsScript.sml`
(`concretize_function_fuel_in_context`, reached through
`execute_configured_fn_pass_concretize` in
`venom/defs/venomPassDispatcherScript.sml`).

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

(*
 ************************************************************
 * DO NOT START THIS PROOF until you have finished and
 * validated ALL the machinery you will need for it.
 * Especially machinery that can be generalized and shared
 * between proofs — write it in separate helper files
 * and build them first.
 *
 * Building generic, powerful abstractions IS explicitly in
 * scope — even if they take significant effort.
 ************************************************************
 *)

The definitions in `ptrDisciplineScript.sml` are weakly frozen: they may
be changed only if the theorem is false with them and the change is the
tightest fix; say so in the report. Everything else outside the new proof
theories is frozen: no change to the pass, the semantics, or the contract
definitions.

## Completion Criteria

1. `holbuild -j4 build concretizeStageSimTheory` passes with zero CHEAT
   warnings and zero failures.
2. No duplicate or near-duplicate lemmas — each helper exists once, in its
   most general form.
3. The INVOKE frame-lifting part of the simulation is stated generically
   (over a relocation of allocation sites and per-instruction step
   obligations), not hard-wired to `concretize_function`: another pass
   (LowerDload, which inserts dead ALLOCAs) will reuse it.

**If the theorem is false as stated:**
- Produce a HOL4 counterexample (`EVAL` on concrete values).
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build concretizeStageSimTheory
```
(from the project root, the directory with `holproject.toml`)

## Background

Stage S5 of the Vyper compiler correctness proof: the O1 Venom pipeline
runs ConcretizeMemLoc on every function, replacing each bump-allocated
`ALLOCA` with a fixed address from a static layout of the call tree
(allocations whose memory-liveness sets don't intersect share space;
callee allocations are imported via `fn_mems_used`). The contract says
every terminating run of the input context is matched by the output
context, and the output only touches memory below the layout end.
`ptr_discipline` is the input fact that makes this true: pointers flow
only into addresses, affine arithmetic, ASSIGN/PHI and pointer
arguments; every access lies inside the allocation its address operand
points into (ghost provenance `G` of `frame_reachable`) and reads only
bytes written since that allocation (ghost `W`).

The old single-function proof
(`concretizeMemLocCorrectnessScript.sml`, `concretize_function_correct`)
is vacuous (its premises quantify over all states/init maps) and
excludes INVOKE; reuse what helps, don't build on its statement.

## Domain Constraints

- holbuild only (no Holmake, no hol4-mcp). Default tactic timeout; never
  raise it. No `TRY`/`ORELSE` around metis or any search tactic.
- No `let` in theorem statements. No new axioms. No cheats left anywhere.
- Executable definitions (the pass, the analyses, the semantics) are
  frozen.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Pointer discipline | venom/compiler/ptrDisciplineScript.sml | frame_reachable, access_ok, ptr_discipline |
| O1 pass contract | venom/compiler/o1PassContractScript.sml | stage contexts, ctx_sim, shape |
| Memory invariant | venom/compiler/unitMemInvScript.sml | mem_inv, phases, mem_inv_transport |
| Raw reachability | venom/codegen/proofs/contextRawReachableScript.sml | raw_reachable (projection of frame_reachable) |
| Pass defs | venom/passes/concretize_mem_loc/defs/concretizeMemLocDefsScript.sml | layout, MemLiveness, allocator |
| Old pass proof | venom/passes/concretize_mem_loc/proofs/concretizeMemLocProofsScript.sml | single-function relation concretize_rel |
| Single-function transport | venom/passes/concretize_mem_loc/proofs/concretizeMemInvTransportScript.sml | mem_inv transport (frame-local) |
| Callee metadata witness | venom/passes/concretize_mem_loc/proofs/calleeMemoryWitnessScript.sml | fn_mems_used example |
| Base pointer analysis | venom/analysis/base_ptr/ | bp_one_pass, partial soundness specs |
| Memory op operands | venom/analysis/shared/defs/memLocDefsScript.sml | mem_write_ops / mem_read_ops |
| Pointer confinement | venom/passes/shared/defs/pointerConfinedDefsScript.sml | pointer_derived_vars, affine_pointer_ops |
| Semantics | venom/defs/venomExecSemanticsScript.sml | step_inst/exec_block/run_blocks (run_defs), exec_alloca, INVOKE helpers |
| Pass dispatcher | venom/defs/venomPassDispatcherScript.sml | execute_configured_fn_pass_*, effects |
| Pass schedule | venom/defs/venomPassScheduleScript.sml | o1_fn_passes order |
| Composition | venom/compiler/o1PipelineComposeScript.sml | how the contract is consumed |

## Notes

- The intuition and the known obligations (analysis fuel, fn_mems_used of
  observed callees, callee accesses inside fn_mems_used) are in the SML
  comment above the theorems.
