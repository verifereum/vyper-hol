# Pass Simulation & Composition Framework

Generic infrastructure for proving compiler pass correctness.

## Structure

```
defs/
  passSimulationDefsScript.sml  — block_map_transform, function_map_transform,
                                   inst_simulates, block_simulates
proofs/
  passSimulationProofsScript.sml — inst_sim_block_sim, block_sim_function,
                                    conditional_inst_sim, block_sim_compose,
                                    result_equiv_trans, lookup_block_map
  passCompositionProofsScript.sml — analysis_pass_correct
passSimulationPropsScript.sml    — re-exports simulation proofs via ACCEPT_TAC
passCompositionPropsScript.sml   — re-exports composition proof via ACCEPT_TAC
```

## Usage

For a 1:1 instruction-mapping pass:
1. Define transform function `f : instruction → instruction`
2. Prove `inst_simulates f` (or use `conditional_inst_sim` for partial transforms)
3. Get block and function correctness for free via `inst_sim_block_sim` + `block_sim_function`

For an analysis-driven pass:
1. Prove dataflow framework conditions (lattice, worklist convergence)
2. Prove analysis fixpoint implies soundness
3. Prove soundness implies block simulation
4. Get function correctness via `analysis_pass_correct`

## Dependencies

Uses `stateEquiv`/`execEquiv` from `venom/` for state and result equivalence.
Uses `worklistProps` from `analysis/dataflow/` for convergence.
