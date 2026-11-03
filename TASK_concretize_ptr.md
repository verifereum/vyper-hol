# TASK: ConcretizeMemLoc output invariants

## Meta
Status: planned
Priority: P0
Created: 2026-11-02
Location: venom/passes/concretize_mem_loc/contract/

## Theorem Statement (FROZEN)

In `venom/passes/concretize_mem_loc/contract/concretizeStagePtrScript.sml`:

```sml
Theorem concretize_stage_ptr:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  ctx_eom_bounded eom C' ==>
  ptr_discipline eom C' vs

Theorem concretize_stage_static_mem:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  ctx_eom_bounded eom C' ==>
  mem_inv (static_mem_ok eom) C' vs
```

Supporting definitions: as in TASK_concretize_sim.md (read its
Theorem section and Background), `ctx_inst_ids_distinct` and
`fn_defs_reach_uses` in `venom/defs/venomWfScript.sml`, `all_reachable` in
`venom/defs/cfgWfScript.sml`, `callee_first` in
`venom/compiler/o1ScheduleDecompScript.sml`, plus `static_mem_ok` and `mem_inv` in
`venom/compiler/unitMemInvScript.sml` and `ctx_eom_bounded` in
`venom/compiler/o1PassContractScript.sml`.

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

The definitions in `ptrDisciplineScript.sml` are weakly frozen: they may
be changed only if a theorem is false with them and the change is the
tightest fix; say so in the report. Everything else outside the new proof
theories is frozen: no change to the pass, the semantics, or the contract
definitions.

## Completion Criteria

1. `holbuild -j4 build concretizeStagePtrTheory` passes with zero CHEAT
   warnings and zero failures.
2. No duplicate or near-duplicate lemmas.

**If a theorem is false as stated:**
- Produce a HOL4 counterexample (`EVAL` on concrete values).
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build concretizeStagePtrTheory
```
(from the project root, the directory with `holproject.toml`)

## Background

ConcretizeMemLoc replaces each `ALLOCA` with an `ASSIGN` of a literal
position from a static layout whose end is the function's `fn_eom`; so the
output C' has no ALLOCA. These two theorems give the next stage
(FmpLowering) its input row: C' keeps the pointer discipline with the
static end `eom` as its fixed-region bound (accesses below `eom` are
unconstrained; DALLOCA regions at or above the free memory pointer are
still sites), and every access is below the
layout end or dynamic (`static_mem_ok eom`).

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

- The stage simulation (`concretize_stage_sim`) is a separate alan task in
  `concretizeStageSimScript.sml`, run in parallel; don't touch that file.
  Put helpers in theories of your own, named `concretizePtr*`.
- Don't use `vs_alloca_next = 0` from `o1_run_state_ok`/`o1_initial_state_ok`:
  it is about to be relaxed so a deploy unit's raw allocator starts at the
  end of its reserved region. Take ALLOCA sites' position from
  `allocas_from lo s` (part of `ptr_discipline`) instead.
- `concretize_stage_ptr` takes `~ctx_has_dalloca C`. Without it the statement
  is false: an uncalled function `a = ALLOCA 32; d = DALLOCA 32;
  q = EQ [a; d]` meets `fn_ptr_ok` in C (both roots, so the compare is
  exempt) but not in C' (`a` is a literal assign, `d` still a root). Don't
  re-derive that counterexample. With the premise, C' has neither ALLOCA nor
  DALLOCA, so `P' = K {}` gives an empty `fn_pv`, and along
  `frame_reachable` in C' the provenance map is `FEMPTY` and
  `vs_allocas = FEMPTY`; `access_ok eom FEMPTY fn` then reduces to the
  `off + len <= eom` bound that `concretize_stage_static_mem` also needs.
- Revert forwarding (`in_revert_forward fn s`: a `RETURNDATACOPY [p; 0; rds]`
  then `REVERT [p; rds]` in one block) is exempt from the range clauses of
  `access_ok` and from `raw_mem_ok`, `static_mem_ok` and `lowered_mem_ok`:
  it copies a callee's revert data to a zero-size site and reverts with
  it, so it touches memory past its site and past the frontier.
