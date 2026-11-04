# TASK: load_elim preserves wf_function and ssa_form

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: venom/passes/load_elim/proofs/loadElimWfScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem load_elim_function_preserves_wf:
  !fn. wf_function fn ==> wf_function (load_elim_function fn)

Theorem load_elim_function_preserves_ssa:
  !fn. wf_function fn /\ ssa_form fn /\
       EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) ==>
       ssa_form (load_elim_function fn)
```

Definitions: `load_elim_function`, `load_elim_one`, `collect_phi_actions`,
`compute_phi_action`, `phis_for_block`, `load_phi_prepend`,
`load_elim_inst`, `fresh_phi_var`, `fresh_phi_id`, `fn_max_inst_id` in
`venom/passes/load_elim/defs/loadElimDefsScript.sml`;
`analysis_function_transform_prepend` in
`venom/simulation/defs/analysisSimDefsScript.sml`; `wf_function`,
`bb_well_formed`, `ssa_form` in `venom/defs/venomWfScript.sml`;
`fn_all_vars` in `venom/defs/cfgTransformScript.sml`.

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

(*
 ************************************************************
 * DO NOT START THIS PROOF until you have finished and
 * validated ALL the machinery you will need for it.
 * Especially machinery that can be generalized and shared
 * between proofs — write it in separate helper files
 * and build them first.
 *
 * Building generic, powerful abstractions (lemmas, tactics,
 * conversions, decision procedures) that help this proof
 * IS explicitly in scope — even if they take significant
 * effort. They amortize across the project.
 ************************************************************
 *)

## Completion Criteria

1. `holbuild -j4 build loadElimWfTheory` passes with zero CHEAT warnings and zero FAILs, at the default tactic timeout.
2. No duplicate or near-duplicate lemmas: search `venom/passes/shared`, `venom/simulation` and `venom/defs` before adding a helper.
3. Only `venom/passes/load_elim/` is edited.

**If the theorem is false as stated:**
- Produce a HOL4 counterexample (e.g., `EVAL_TAC` on concrete values).
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build loadElimWfTheory
```

## Background

`load_elim_function` is Vyper's Venom load-elimination pass (O2/O3). It
runs five rounds (memory, transient, storage, dload, calldataload), each
replacing redundant loads by ASSIGNs, redundant stores by NOPs, and
inserting PHIs at join blocks, then drops NOPs. Later passes need its
output to stay well-formed and in SSA form.

## Domain Constraints

- Never raise the tactic timeout; a step that runs over is a proof bug: split it.
- No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`.
- No `let` in theorem statements; no `cheat` left behind.
- Theories go in `Ancestors`, not `load`.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Pass defs | venom/passes/load_elim/defs/loadElimDefsScript.sml | the pass |
| Target | venom/passes/load_elim/proofs/loadElimWfScript.sml | statements, intuition in comments |
| Transform framework | venom/simulation/defs/analysisSimDefsScript.sml, venom/simulation/analysisSimPropsScript.sml (and siblings under venom/simulation) | `analysis_function_transform_prepend`, `function_map_transform` and their lemmas |
| Shared pass lemmas | venom/passes/shared/passSharedPropsScript.sml | `clear_nops_function_preserves_wf`, `clear_nops_block_preserves_wf`, mk_assign/mk_nop facts |
| Shared pass defs | venom/passes/shared/defs/passSharedDefsScript.sml | `mk_assign_inst`, `mk_nop_inst`, `clear_nops_function` |
| wf defs and lemmas | venom/defs/venomWfScript.sml | `wf_function`, `bb_well_formed`, `ssa_form`, `fn_inst_ids_distinct` |
| Var listing | venom/defs/cfgTransformScript.sml | `fn_all_vars` |
| Similar preservation proofs | grep -rn "preserves_wf\|preserves_ssa" venom/passes | e.g. other passes' wf/ssa preservation, to reuse patterns and helpers |

## Notes

- `loadElimWfTheory` builds with the cheats (statements parse).
