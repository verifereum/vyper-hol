# TASK: assemble dft_ctx_sim_gas from the oracle pieces

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/compiler

## Theorem Statement (FROZEN)

In `venom/compiler/dftContractGasScript.sml`:

```sml
Theorem dft_ctx_sim_gas:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C vs'.vs_labels /\ o1_run_state_ok vs' ==>
  ?vs. gas_variant vs vs' /\ ctx_sim D C C' vs vs' /\
       (o1_lowered_inv C vs ==> o1_lowered_inv C' vs')
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

The definitions in `venom/compiler/dftGasOracleDefsScript.sml` are frozen too: don't edit that file.

## Completion Criteria

1. `holbuild -j4 build dftContractGasTheory` passes from the project root at the default tactic timeout.
2. `venom/compiler/dftContractGasScript.sml` has no `cheat` (the four cheated ancestors are expected; see Notes).
3. No duplicate or near-duplicate lemmas; each helper exists once, in its most general form.

**If the theorem is false as stated:** give a HOL4 counterexample (EVAL on concrete values in a scratch theory), state the tightest sufficient fix, and don't weaken the statement.

## Build

```
holbuild -j4 build dftContractGasTheory
```

## Background

DFT (instruction scheduling within blocks) may move a GAS read past another GAS read or an INVOKE, so the scheduled context C' consumes the state's gas reading list in another order than C. This theorem: for the run of C' from vs', some gas variant vs of vs' (differing only in vs_gas_readings) makes C from vs simulate into C' from vs' (ctx_sim), and carries the lowered memory invariant from C to C'. It is assembled from four pieces stated in its ancestors and proved separately at the same time (they are cheated on this branch; use them as given): gas_oracle_from_list (dftGasOracleFromList), gas_oracle_to_list (dftGasOracleToList), dft_ev_context_sim (dftGasOracleSim), dft_ev_lowered_inv (dftGasOracleInv), over the oracle semantics of dftGasOracleDefs. The comment above dft_ctx_sim_gas sketches the assembly.

## Domain Constraints

- holbuild only, at most `-j4`. Never raise the tactic timeout, never pass `--skip-checkpoints`, never wrap metis or other search in `TRY` or `ORELSE`.
- Don't edit any existing theory. Put helpers in new theories under `venom/compiler/` whose names start with `dftGasAsm` (other provers work on sibling pieces at the same time and use other prefixes), and keep each under about 500 lines.
- Theories go in `Ancestors`, `Theorem ... Proof ... QED` syntax, no `let` in statements, `rename1` instead of generated names (AGENTS.md).
- Avoid the variable name `O` (relation composition) and keyword-like names (`fn` is fine in statements, see existing code).

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| oracle semantics (frozen defs) | venom/compiler/dftGasOracleDefsScript.sml | ev_step/ev_block/ev_blocks/ev_function/ev_context, ev_reachable, gas_res_rel |
| list semantics | venom/defs/venomExecSemanticsScript.sml | run_defs (step_inst/exec_block/run_blocks), run_function_def, run_context_def, exec_gas_def, step_inst_base_def, merge_callee_state_def, setup_callee_def |
| semantics facts | venom/defs/venomExecProofsScript.sml, venom/props/ | fuel_mono etc. |
| raw_reachable | venom/codegen/proofs/contextRawReachableScript.sml | the list-semantics reachability inductive ev_reachable mirrors |
| active_inst, enters_block | venom/codegen/defs/contextCodegenRelScript.sml | |
| gas_variant | venom/compiler/o1PassContractScript.sml | states equal up to vs_gas_readings |
| GAS reading facts | venom/proofs/gasOracleReplayScript.sml, venom/proofs/gasCountScript.sml, venom/proofs/gasEventsScript.sml | readings only affect GAS; gas_oracle_replay; gas_count_fuel_mono; per-run GAS event lists |
| project rules | AGENTS.md, docs/HOL4_PROOF_CONTROL_LESSONS.md | conventions |
| the four pieces | venom/compiler/dftGasOracle{FromList,ToList,Sim,Inv}Script.sml | frozen statements, cheated here |
| target and its context | venom/compiler/dftContractGasScript.sml, venom/compiler/o1PassContractScript.sml | ctx_sim_def, gas_variant_def, o1_lowered_inv_def, lowered_mem_fact_def, o1_ctx_shape_def, o1_run_state_ok_def, dead_result_rel (venom/compiler/ptrDisciplineScript.sml) |
| no IntRet | venom/props/venomRetPropsScript.sml | run_context_not_int_ret; entry_fn_no_return in o1PassContract |
| memory invariant | venom/compiler/unitMemInvScript.sml | mem_inv_raw_reachable, lowered_mem_ok_def, inst_mem_ranges_def |
| max_live_eom | venom/codegen/defs/stackPlanGenScript.sml | max_live_eom_def, collect_fn_eoms |
| DFT | venom/passes/dft/defs/dftDefsScript.sml, venom/passes/dft/proofs/dftRunRelScript.sml, venom/passes/dft/proofs/dftCorrectnessFinalScript.sml, venom/passes/dft/proofs/dftLiftingScript.sml | dft_fn, dft_fn_rel_def (wf_function), dft_res_rel_def, dft_fn_entry_label, dft_fn_labels_map, bb_inst_ids_distinct |

## Notes

The four pieces are cheated on this branch, so theorems that use them carry the cheat tag; that is expected. What must hold is that venom/compiler/dftContractGasScript.sml itself has no cheat and that you don't edit the four piece files or dftGasOracleDefs. The other theorems already in dftContractGasScript.sml must keep building.
