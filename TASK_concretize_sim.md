# TASK: ConcretizeMemLoc stage simulation

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
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  dead_wf D /\ taint_within D C vs /\ EVERY ssa_form C.ctx_functions /\
  ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions ==>
  ctx_sim_dead D C C' vs

Theorem concretize_stage_taint:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  dead_wf D /\ taint_within D C vs /\ EVERY ssa_form C.ctx_functions /\
  ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions ==>
  taint_within D C' vs
```

Supporting definitions: `ptr_discipline`, `frame_reachable`, `access_ok`,
`taint_ok`, `fn_ptr_ok`, `fixed_region_reserved`, `taint_within`, `dead_wf`,
`dead_result_rel`, `ctx_sim_dead` in `venom/compiler/ptrDisciplineScript.sml`; `ctx_pass_stage`,
`o1_walk_view`, `walk_view`, `fn_pass_step`, `fn_steps`, `ctx_sim`,
`o1_ctx_shape`, `ctx_eom_bounded` in `venom/compiler/o1PassContractScript.sml`;
`mem_inv`, `raw_mem_ok`, `static_mem_ok`, `inst_mem_ranges` in
`venom/compiler/unitMemInvScript.sml`; the pass in
`venom/passes/concretize_mem_loc/defs/concretizeMemLocDefsScript.sml`
(`concretize_function_fuel_in_context`, reached through
`execute_configured_fn_pass_concretize` in
`venom/defs/venomPassDispatcherScript.sml`); `ctx_has_dalloca` in
`ptrDisciplineScript.sml`; `ctx_inst_ids_distinct` and `fn_defs_reach_uses`
in `venom/defs/venomWfScript.sml`, `all_reachable` in
`venom/defs/cfgWfScript.sml`, `callee_first` in
`venom/compiler/o1ScheduleDecompScript.sml`.

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
tightest fix; say so in the report. The premises are frozen except for one allowance: if the analyses'
convergence within their fuel or the base-pointer analysis's soundness
needs definitions to dominate their uses, you may add the tightest such
premise, preferring the existing `def_available_at`
(venom/defs/venomWfScript.sml), and say so in the report. Everything else
outside the new proof theories is frozen: no change to the pass, the semantics, or the contract
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
only into addresses, affine arithmetic, ASSIGN/PHI, pointer arguments and
compares of two pointers into the same site; every write above the fixed
region `lo` lies inside the allocation its address operand points into
(ghost provenance `G` of `frame_reachable`), and every byte that is fresh
(never written since its allocation) is tainted (ghost `tn`).
Tainted data only moves (ASSIGN, stores of the value, MLOAD/MCOPY/RETURN),
never decides anything, and `taint_within D` says it only ever reaches
storage/transient/immutables/return-data bytes in `D`, which the result
relation `dead_result_rel D` doesn't compare. Hence the conclusion is
`ctx_sim_dead D`, not exact equivalence: the packed run reads stale bytes
where the raw run read zeros, and they may reach dead storage bytes.

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
- Statement amended after three counterexamples (all checked, approved):
  (1) `collision_static_counterexample` (concretizePtrCollisionReachScript.sml):
  two callees share ALLOCA inst id 100 with different sizes, so the
  pass's by-id dedup reserves only the first; now excluded by
  `ctx_inst_ids_distinct C`. (2) a dead block's ALLOCA with a short
  liveset packed below a live one pushes it onto a DALLOCA at
  vs_initial_fmp; now excluded by `~ctx_has_dalloca C` on all four
  lemmas. (3) `v = PHI [p; a1]` with `p` a PARAM gets a singleton
  points-to set, so a store through `v` must-kills `a1` and a live `a2`
  is packed onto it; now excluded by `fn_ptr_ok`'s write-exclusion
  clause: no memory-write offset `Var v` is both alloca-derived and
  PARAM/DALLOCA-derived (with `phi_pv_all_var fn (ptr_roots P fn)`).
  Mixed non-store pointers are allowed, since IfExp over a memory param
  and a literal ASSIGNs both into one var. `callee_first` (call-DAG induction),
  `all_reachable` and `fn_defs_reach_uses` were added as premises
  because the rows carry them; use them freely.

- `concretize_stage_taint` follows the same simulation: the output's taint at
  matching steps is at most the input's, and `dead_wf D` moves `D` across the
  states that agree outside it.
- The output invariants (`concretize_stage_ptr`, `concretize_stage_static_mem`)
  are a separate task in `concretizeStagePtrScript.sml`
  (TASK_concretize_ptr.md), run in parallel; don't touch that file.
  Layout facts both need (positions avoid `ctx_global_reserved`, sites
  that are live together don't overlap) go in a helper theory of your own;
  name it `concretizeLayout*` and say so in your report.
- The REVERT exemption (`about_to_revert`): a REVERT, and a RETURNDATACOPY
  right before one, may read tainted memory; both runs then revert, and
  `dead_result_rel` doesn't compare revert payloads.
- Revert forwarding (`in_revert_forward fn s`: a `RETURNDATACOPY [p; 0; rds]`
  then `REVERT [p; rds]` in one block) is exempt from `access_ok`'s range
  clauses and from the raw and static memory facts: both runs revert there.

- The intuition and the known obligations (analysis fuel, fn_mems_used of
  observed callees, callee accesses inside fn_mems_used) are in the SML
  comment above the theorems.
- Forced alloca positions: an input with two forced, simultaneously live
  allocas at the same position is a counterexample (seen in an earlier run).
  `fn_ptr_ok` now requires `fn.fn_forced_alloc_positions = FEMPTY`, which
  rules it out; the frozen statements are unchanged.
- Don't use `vs_alloca_next = 0` from `o1_run_state_ok`/`o1_initial_state_ok`:
  it is about to be relaxed so a deploy unit's raw allocator starts at the
  end of its reserved region. Take ALLOCA sites' position from
  `allocas_from lo s` (part of `ptr_discipline`) instead.
