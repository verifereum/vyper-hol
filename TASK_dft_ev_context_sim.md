# TASK: DFT simulation in the oracle semantics (dft_ev_context_sim)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/compiler

## Theorem Statement (FROZEN)

In `venom/compiler/dftGasOracleSimScript.sml`:

```sml
Theorem dft_ev_context_sim:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C s.vs_labels /\ o1_run_state_ok s /\
  terminates (ev_context orc fuel C s) ==>
  dft_res_rel (ev_context orc fuel C s) (ev_context orc fuel C' s)
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

The definitions in `venom/compiler/dftGasOracleDefsScript.sml` are frozen too: don't edit that file.

## Completion Criteria

1. `holbuild -j4 build dftGasOracleSimTheory` passes from the project root at the default tactic timeout.
2. `venom/compiler/dftGasOracleSimScript.sml` has no `cheat`, and its theory's build log (`.holbuild/logs/current/vyper-hol/dftGasOracleSimTheory/build.log`) has no CHEAT warning for a theorem of that file.
3. No duplicate or near-duplicate lemmas; each helper exists once, in its most general form.

**If the theorem is false as stated:** give a HOL4 counterexample (EVAL on concrete values in a scratch theory), state the tightest sufficient fix, and don't weaken the statement.

## Build

```
holbuild -j4 build dftGasOracleSimTheory
```

## Background

DFT reorders instructions within each block of each function (dft_fn). In the oracle semantics of dftGasOracleDefs a GAS read gets the oracle's word for its event (frame path, block depth, GAS id), which DFT keeps, so GAS behaves like a pure read there. This theorem: every terminating oracle run of C is matched, at the same oracle and fuel, by the run of its DFT schedule C' (dft_res_rel: equal OK/IntRet/Halt states, an Abort for an Abort with Revert kept). It is one of four pieces of the proof of dft_ctx_sim_gas (venom/compiler/dftContractGasScript.sml).

## Domain Constraints

- holbuild only, at most `-j4`. Never raise the tactic timeout, never pass `--skip-checkpoints`, never wrap metis or other search in `TRY` or `ORELSE`.
- Don't edit any existing theory. Put helpers in new theories under `venom/compiler/` whose names start with `dftGasSim` (other provers work on sibling pieces at the same time and use other prefixes), and keep each under about 500 lines.
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
| DFT pass | venom/passes/dft/defs/dftDefsScript.sml | dft_block, dft_fn, dft_eda, entry_instructions, abort-run deps |
| DFT block-level results | venom/passes/dft/proofs/dftRunRelScript.sml | dft_res_rel_def, dft_fn_rel_def, ctx_labels_bound_def, dft_run_block_gas (block-level list-semantics simulation, same callee context), commutation lemmas |
| DFT schedule order | venom/passes/dft/proofs/dftScheduleOrderScript.sml | dft_block_rel, dft_must_order, dft_fallible_order_kept |
| other DFT proofs | venom/passes/dft/proofs/ | dftBlockSim, dftCommutation, dftLifting (dft_fn_block_rel), dftStructural, dftAbortOrder, dftCorrectnessFinal (dft_fn_entry_label, dft_fn_labels_map) |
| stage context | venom/compiler/o1PassContractScript.sml, venom/compiler/unitShapeDefsScript.sml | o1_ctx_shape_def, o1_fn_shape_def, o1_run_state_ok_def, lowered_mem_fact_def; inst_shape_ok (l.304) bans DELEGATECALL, CREATE, CREATE2, SELFDESTRUCT, DJMP, OFFSET |
| DFT stage facts | venom/compiler/dftContractGasScript.sml, venom/compiler/o1DftStepScript.sml | ctx_pass_stage_dft, dft_fn_rel_stage, dft_shape_* |

## Notes

The statement was checked against the definitions by a reviewer, who found it true. Its note: o1_run_state_ok does not hold in callee frames (vs_fmp moves), so anything proved per frame needs hypotheses that callees keep (~cc_static, ctx_labels_bound). A sibling piece (dft_ev_lowered_inv, branch of its own) may want this simulation without the terminates hypothesis (dft_res_rel's Error clause); if you prove such a general form on the way, keep it as its own theorem.
