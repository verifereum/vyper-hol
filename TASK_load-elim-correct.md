# TASK: load_elim_function_correct_proof

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: venom/passes/load_elim/proofs/loadElimProofsScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem load_elim_function_correct_proof:
  !fuel ctx fn s.
    wf_function fn /\
    fn_inst_wf fn /\
    wf_ssa fn /\
    EVERY (\v. ~isPREFIX "$le_phi_" v) (fn_all_vars fn) /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    dfg_assigns_sound (dfg_build_function fn) s /\
    bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) s /\
    alloca_inv s /\
    allocas_in_word s /\
    bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn s /\
    bp_phis_closed (bp_analyze (cfg_analyze fn) fn) fn /\
    bp_assigns_stable (bp_analyze (cfg_analyze fn) fn) (dfg_build_function fn) /\
    (!bb s0 s_phi.
       MEM bb fn.fn_blocks /\
       MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
       eval_phis s0 bb.bb_instructions = OK s_phi /\
       dfg_assigns_sound (dfg_build_function fn) s0 ==>
       dfg_assigns_sound (dfg_build_function fn) s_phi) /\
    (!fuel' run_ctx bb inst s0 s1.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       inst_wf inst /\
       dfg_assigns_sound (dfg_build_function fn) (s0 with vs_inst_idx := 0) /\
       bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) (s0 with vs_inst_idx := 0) /\
       allocas_non_overlapping (s0 with vs_inst_idx := 0) /\
       allocas_in_word (s0 with vs_inst_idx := 0) /\
       bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn (s0 with vs_inst_idx := 0) /\
       step_inst fuel' run_ctx inst s0 = OK s1 ==>
       dfg_assigns_sound (dfg_build_function fn) (s1 with vs_inst_idx := 0) /\
       bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) (s1 with vs_inst_idx := 0) /\
       allocas_non_overlapping (s1 with vs_inst_idx := 0) /\
       allocas_in_word (s1 with vs_inst_idx := 0) /\
       bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn (s1 with vs_inst_idx := 0)) /\
    LENGTH s.vs_memory < dimword (:256) ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv {v | isPREFIX "$le_phi_" v})
      (execution_equiv {v | isPREFIX "$le_phi_" v})
      (execution_equiv {v | isPREFIX "$le_phi_" v})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (load_elim_function fn) s)
```

Definitions: the pass (`load_elim_function`, `load_elim_one`,
`load_analyze`, `collect_phi_actions`, `compute_phi_action`,
`find_join_block`, `phis_for_block`, `load_elim_inst`, `fresh_phi_var`)
in `venom/passes/load_elim/defs/loadElimDefsScript.sml`;
`analysis_function_transform_prepend` in
`venom/simulation/defs/analysisSimDefsScript.sml`; `state_equiv`,
`execution_equiv`, `lift_result` in `venom/defs/stateEquivScript.sml`
(grep if moved); `dfg_assigns_sound` in
`venom/analysis/dfg/proofs/dfgCorrectnessProofScript.sml`;
`bp_assigns_stable`, `allocas_in_word` in
`venom/passes/memory_copy_elision/proofs/memoryCopyElisionSoundScript.sml`;
`bp_ptr_sound`, `bp_ptrs_bounded`, `bp_phis_closed` in
`venom/analysis/base_ptr/defs/basePtrDefsScript.sml`; `alloca_inv`,
`allocas_non_overlapping` in `venom/defs/venomMemDefsScript.sml`.

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

1. `holbuild -j4 build loadElimProofsTheory` passes with zero CHEAT warnings and zero FAILs, at the default tactic timeout.
2. No duplicate or near-duplicate lemmas: search `venom/passes/shared`, `venom/simulation`, `venom/analysis` and the proved memory passes before adding a helper.
3. Only `venom/passes/load_elim/` is edited (new helper theories may go in `venom/passes/load_elim/proofs/`).

**If the theorem is false as stated:**
- Produce a HOL4 counterexample (e.g., `EVAL_TAC` on concrete values).
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
holbuild -j4 build loadElimProofsTheory
```

## Background

`load_elim_function` is Vyper's Venom load-elimination pass (O2/O3). Five
rounds (memory, transient, storage, dload, calldataload) each replace a
load whose value the dataflow lattice knows by an ASSIGN of that value,
or of a new PHI (output `$le_phi_<load id>`, inserted at the join block)
when predecessors provide different known values; redundant stores
become NOPs; NOPs are dropped at the end. The theorem says the
transformed function behaves like the original, up to the new PHI
variables. Its premise set is `copy_elision_function_correct`'s (a
proved pass using the same base-pointer analysis) plus freshness of the
`$le_phi_` prefix.

## Domain Constraints

- Never raise the tactic timeout; a step that runs over is a proof bug: split it.
- No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`.
- No `let` in theorem statements; no `cheat` left behind.
- Theories go in `Ancestors`, not `load`.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Pass defs | venom/passes/load_elim/defs/loadElimDefsScript.sml | the pass and its analysis |
| Target | venom/passes/load_elim/proofs/loadElimProofsScript.sml | statement, notes in comments |
| wf/ssa preservation | venom/passes/load_elim/proofs/loadElimWfScript.sml | the output stays wf_function / ssa_form (proved separately; may be cheated while that proof runs, so use it only as an ancestor) |
| Closest proved pass | venom/passes/memory_copy_elision/ (memoryCopyElisionCorrectnessScript.sml, proofs/memoryCopyElisionSoundScript.sml, proofs/memoryCopyElisionProofsScript.sml) | same premises; memory/alias soundness, dfg and bp invariants carried through run_blocks |
| Other proved passes | venom/passes/simplify_cfg, single_use_expansion, dft, concretize_mem_loc | simulation patterns |
| Simulation framework | venom/simulation/ (analysisSimDefs, analysisSimProps, passSimulationDefs, passSimulationProps) | analysis_inst_simulates, prepend transforms, block/function simulation lemmas |
| Shared pass lemmas | venom/passes/shared/ | mk_assign_inst / mk_nop_inst / clear_nops simulation |
| DFG | venom/analysis/dfg/ | normalize_operand, dfg_assigns_sound and its lemmas |
| Base pointers | venom/analysis/base_ptr/ (defs/basePtrDefsScript.sml, basePtrPropsScript.sml) | bp_analyze, soundness |
| Alias analyses | grep -rn "memory_alias_analyze\|storage_alias_analyze" venom | alias analysis defs and soundness |
| Memory model | venom/defs/venomMemDefsScript.sml and venomMem* | allocas, memory invariants |
| Semantics | venom/defs/venomExecSemanticsScript.sml, venom/defs/venomStateScript.sml | run_blocks, step_inst, eval_phis |
| State equivalence | grep -rn "Definition state_equiv" venom | state_equiv, execution_equiv, lift_result and props |

## Notes

- `loadElimProofsTheory` builds with the cheat (statement parses).
- The earlier statement (only `fn_inst_wf`, `inst_idx = 0`, arbitrary bp) was false: start mid-function, overlapping allocas under an arbitrary bp, and non-SSA input each break it.
