# TASK: ConcretizeMemLoc output static-memory bound

## Meta
Status: planned
Priority: P0
Created: 2026-11-02 (restated 2026-11-05)
Location: venom/passes/concretize_mem_loc/contract/

## Theorem Statement (FROZEN)

In `venom/passes/concretize_mem_loc/contract/concretizeStageStaticScript.sml`:

```sml
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
  max_live_eom C' = SOME eom ==>
  mem_inv (static_mem_ok eom) C' vs
```

Supporting definitions: `max_live_eom` and `collect_fn_eoms` in
`venom/codegen/defs/stackPlanGenScript.sml` (so `eom` is the maximum of the
global reserved end and every function's `fn_eom` in C', each of which is
`SOME`); `global_reserved_end` in
`venom/passes/concretize_mem_loc/defs/staticLayoutDefsScript.sml`;
`static_mem_ok` and `mem_inv` in `venom/compiler/unitMemInvScript.sml`;
`fixed_region_reserved`, `ptr_discipline`, `access_ok` in
`venom/compiler/ptrDisciplineScript.sml`; `ctx_inst_ids_distinct` and
`fn_defs_reach_uses` in `venom/defs/venomWfScript.sml`; `all_reachable` in
`venom/defs/cfgWfScript.sml`; `callee_first` in
`venom/compiler/o1ScheduleDecompScript.sml`; the stage relation in
`venom/compiler/o1PassContractScript.sml`.

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

Everything outside the proof theories is frozen: the pass, the analyses, the
semantics, the contract definitions, `ptrDisciplineScript.sml` and every
other existing theory of the project that is not one of this run's own
helper theories.

## Completion Criteria

1. `holbuild -j4 build concretizeStageStaticTheory` passes with zero CHEAT
   warnings and zero failures.
2. No duplicate or near-duplicate lemmas.

**If the theorem is false as stated:**
- Produce a HOL4 counterexample (`EVAL` on concrete values).
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build concretizeStageStaticTheory
```
(from the project root, the directory with `holproject.toml`)

## Background

ConcretizeMemLoc replaces each `ALLOCA` with an `ASSIGN` of a literal
position from a static layout whose end is the function's `fn_eom`; so the
output C' has no ALLOCA (and, with `~ctx_has_dalloca C`, no DALLOCA). This
theorem gives the next stage (FmpLowering) the memory half of its input row:
every access of C' along a reachable state is below the context's layout end
`eom = max_live_eom C'`, or part of a revert forwarding (`static_mem_ok eom`).

## Domain Constraints

- holbuild only (no Holmake, no hol4-mcp). Default tactic timeout; never
  raise it. No `TRY`/`ORELSE` around metis or any search tactic.
- No `let` in theorem statements. No new axioms. No cheats left anywhere.
- Executable definitions (the pass, the analyses, the semantics) are
  frozen.
- New helper theories go under `venom/passes/concretize_mem_loc/proofs/`
  (or, for pass-independent facts, new files under
  `venom/passes/shared/proofs/`). This run's own earlier helper theories,
  including those it added under `venom/compiler/` (`frame*Script.sml`,
  `ptrDisciplineEmptyTaintScript.sml`), may be edited; no other existing
  theory may.
- Do not touch `concretizeStageSimScript.sml`, `concretizeStageShapeScript.sml`
  or `concretizeStepContractScript.sml`: they are other workers' targets.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Pointer discipline | venom/compiler/ptrDisciplineScript.sml | frame_reachable, access_ok, ptr_discipline |
| O1 pass contract | venom/compiler/o1PassContractScript.sml | stage contexts, o1_static_inv (the row this feeds) |
| Memory invariant | venom/compiler/unitMemInvScript.sml | mem_inv, static_mem_ok |
| Layout end | venom/codegen/defs/stackPlanGenScript.sml | max_live_eom, collect_fn_eoms |
| Raw reachability | venom/codegen/proofs/contextRawReachableScript.sml | raw_reachable (projection of frame_reachable) |
| Pass defs | venom/passes/concretize_mem_loc/defs/concretizeMemLocDefsScript.sml | layout, MemLiveness, allocator |
| Static layout defs | venom/passes/concretize_mem_loc/defs/staticLayoutDefsScript.sml | global_reserved_end |
| This run's helpers | venom/passes/concretize_mem_loc/proofs/concretizePtr*Script.sml and the other theories this run added | reuse them |
| Old pass proof | venom/passes/concretize_mem_loc/proofs/concretizeMemLocProofsScript.sml | single-function relation concretize_rel |
| Base pointer analysis | venom/analysis/base_ptr/ | bp_one_pass, partial soundness specs |
| Pointer confinement | venom/passes/shared/defs/pointerConfinedDefsScript.sml | pointer_derived_vars, affine_pointer_ops |
| Semantics | venom/defs/venomExecSemanticsScript.sml | step_inst/exec_block/run_blocks, INVOKE helpers |
| Pass dispatcher | venom/defs/venomPassDispatcherScript.sml | execute_configured_fn_pass_* |

## Notes
- RESTATEMENT (2026-11-05). This task used to freeze two theorems in
  `concretizeStagePtrScript.sml`, `concretize_stage_ptr` and
  `concretize_stage_static_mem`, with the premise `ctx_eom_bounded eom C'`.
  `ctx_eom_bounded` was never defined (a free variable), so nothing could be
  derived from it. Now:
  (1) the only target is `concretize_stage_static_mem`, in
  `concretizeStageStaticScript.sml`; `concretize_stage_ptr` and the file
  `concretizeStagePtrScript.sml` are gone, and work that only served the
  pointer-discipline conclusion (empty output ghosts, `ptr_discipline eom C'`)
  is no longer needed;
  (2) the premise is `max_live_eom C' = SOME eom`: `eom` is at least every
  output function's `fn_eom` (all `SOME`) and the global reserved end, and
  `fixed_region_reserved lo C` puts every address below `lo` inside a global
  reserved interval, so below `eom` too.
  The PLAN's obligations that waited on a usable eom bound (strict target
  endpoints from successful layouts, then `fn_eom <= eom`) can now use it.
- The project was moved to a newer base (it gained the GAS join and static
  frames); a helper theory that no longer builds there is to be repaired,
  not dropped.
- Statement was earlier amended after three counterexamples (all checked,
  approved): (1) `collision_static_counterexample`: two callees share ALLOCA
  inst id 100 with different sizes, so the pass's by-id dedup reserves only
  the first; excluded by `ctx_inst_ids_distinct C`. (2) a dead block's
  ALLOCA with a short liveset packed below a live one pushes it onto a
  DALLOCA at vs_initial_fmp; excluded by `~ctx_has_dalloca C`. (3)
  `v = PHI [p; a1]` with `p` a PARAM gets a singleton points-to set, so a
  store through `v` must-kills `a1` and a live `a2` is packed onto it;
  excluded by the two `phi_pv_all_var` clauses of `fn_ptr_ok`. Don't
  re-derive them.
- Don't use `vs_alloca_next = 0` from `o1_run_state_ok`/`o1_initial_state_ok`.
  Take ALLOCA sites' position from `allocas_from lo s` (part of
  `ptr_discipline`) instead.
