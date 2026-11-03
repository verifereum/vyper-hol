# TASK: DFT simulates its input up to a reordering of the gas readings

## Meta
- Project: vyper-hol (HOL4, holbuild)
- Script: venom/compiler/o1ContractDftScript.sml
- Theory: o1ContractDftTheory

## Theorem Statement (FROZEN)

```sml
Theorem dft_ctx_sim_gas:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\
  ctx_labels_bound C vs'.vs_labels /\ o1_run_state_ok vs' ==>
  ?vs. gas_variant vs vs' /\ ctx_sim D C C' vs vs' /\
       (o1_lowered_inv C vs ==> o1_lowered_inv C' vs')
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

Weakly frozen intermediate (venom/passes/dft/proofs/dftRunRelScript.sml,
currently `cheat`): `dft_run_block_gas`, one block in the same context, up
to a gas variant of the start state, under the readiness and abort-order
premises. Prove it as stated; if it turns out false or unusable, stop and
report why rather than changing it. `dft_ctx_sim_gas` relates C and C',
whose INVOKE callees differ (fn vs dft_fn fn), so either parameterize a
block lift over (C, C') with a callee hypothesis for INVOKE, or lift
directly through the run relation; that choice is yours.

## Completion Criteria
- `dft_ctx_sim_gas` and `dft_run_block_gas` proved with no `cheat`,
  statements byte-identical.
- No new axioms, no `cheat` in any theorem you add, no new hypotheses on the frozen statement.
- New helper theorems and theories are fine (put DFT-specific facts under
  venom/passes/dft/proofs/ or venom/compiler/, registered the way neighbouring
  theories are).
- The cheats in venom/passes/dft/proofs/dftBlockSimScript.sml
  (`gas_pair_commute`, `independent_commute_eq`,
  `output_var_agree_across_independent`) are being proved by a separate run;
  use their statements, don't edit that file.
- The other cheated theorems in o1ContractDftScript.sml (`dft_ctx_labels_bound`,
  `dft_fn_rel_stage`, `dft_out_wf_ssa`, `dft_contract_gas`) are out of scope;
  leave them as they are.

## Build
From the project root:

```
holbuild -j4 build o1ContractDftTheory
```

## Background
- DFT (`dft_fn`, venom/passes/dft/defs/dftDefsScript.sml) reschedules the
  instructions of each block. `dft_fn_rel` (venom/passes/dft/proofs/dftRunRelScript.sml)
  bundles what the caller knows of each function pair: SSA, wf, pseudos
  prefix, no ALLOCA, the block relation `dft_block_rel` (what DFT keeps in
  order, proved in dftScheduleOrderScript.sml as `dft_fn_block_rel`) and
  `dft_fallible_order_kept`.
- GAS has no effects (venom/defs/venomEffectsScript.sml), so DFT may move it
  past other GAS reads and past INVOKE. GAS consumes `vs_gas_readings`
  (`exec_gas`, venom/defs/venomExecSemanticsScript.sml), reading 0 once the
  list is empty. So C' consumes the readings in another order than C. That is
  why the input state is existential: a gas variant of vs' (`gas_variant`,
  equal except for `vs_gas_readings`).
- Intended witness: the readings C' takes along its run from vs', permuted
  into the order C reads them, then the unread tail. C then takes the same
  path with the same fuel, ends with a result `dead_result_rel` accepts, and
  every state C' reaches has a C-reachable counterpart with the same memory
  and the same operand values at memory instructions, which carries
  `mem_inv` (`mem_inv` is equivalent to a statement over `raw_reachable`
  states, unitMemInvScript.sml).
- The hard case is a C' run that never terminates: `ctx_sim` quantifies over
  every fuel after the witness is fixed, and `mem_inv` covers states of
  divergent runs too. Only finitely many readings exist, so a finite witness
  exists; reads only C makes (e.g. a GAS that C' would make after a callee
  that diverges) can get any value, since everything moved across an INVOKE
  is effect-free and the terminator stays last.
- `venom/proofs/gasOracleReplayScript.sml` (`gas_oracle_replay`) replays a
  finite run of step_inst / exec_block / run_blocks from its consumed prefix
  plus any tail, with all other fields equal.
- `dft_res_rel` and the block relation helpers in dftRunRelScript.sml, the
  schedule facts in dftScheduleOrderScript.sml, and dftCommutationScript.sml /
  dftPermSimScript.sml / dftBlockSimScript.sml / dftIndexedExecScript.sml are the existing DFT
  execution infrastructure.

- The same-state version of the block lift for the old (constant) GAS
  semantics is being proved on git branch `bot/opus/seq-515-dft-contract`
  (`dft_run_block_same_context` in dftRunRelScript.sml, with helper theories
  dftAvailability, dftSuccessSwap, dftStoppingSwap). Read it with
  `git show bot/opus/seq-515-dft-contract:<path>` and reuse its structure;
  it is not in this checkout.
- DFT's old `full_dep`-based execution proof was dropped from
  dftCorrectnessScript.sml: its premise `dft_schedule_safe` is false
  (`dft_schedule_safe_false`), so `dft_pass_correct` is closed vacuously.
- `gas_pair` (dftBlockSim) names the pairs that both consume readings: GAS x
  GAS, GAS x INVOKE. `bi_independent` / `ext_bi_independent` (dftPermSim)
  exclude them; `gas_pair_commute` commutes them up to a gas variant.

## Domain Constraints
- Don't change any definition under venom/defs/, venom/passes/dft/defs/,
  `gas_pair_def`, `bi_independent_def`, `ext_bi_independent_def`,
  venom/compiler/o1PassContractScript.sml or venom/compiler/o1PassLiftScript.sml.
- Don't raise the tactic timeout; no `TRY`/`ORELSE` around metis or other search.
- Theorems consumed outside their own theory keep their statements.

## Available Resources
- venom/compiler/o1PassContractScript.sml: `ctx_sim`, `dead_result_rel`,
  `gas_variant`, `o1_lowered_inv`, `o1_run_state_ok`, `o1_ctx_shape`.
- venom/compiler/unitMemInvScript.sml: `mem_inv`, `lowered_mem_fact`,
  `ctx_eom_bounded`, `mem_inv_raw_reachable`.
- venom/codegen/defs/contextRawReachableScript.sml, contextCodegenRelScript.sml:
  `raw_reachable`, `inst_mem_ranges`.
- venom/compiler/o1PassLiftScript.sml: `frame_reach`, `mem_corr`,
  `mem_corr_closed`, `frame_sim_mem_inv` (same-state; a pattern, not directly
  usable here).
- venom/proofs/gasOracleReplayScript.sml: `gas_oracle_replay`, `gas_prefix`.
- venom/passes/dft/proofs/: the DFT proof theories listed above.
- venom/defs/venomExecSemanticsScript.sml: `run_blocks`, `exec_block`,
  `step_inst`, `run_context`, `exec_gas`, `setup_callee`.

## Notes
- Fuel: `run_blocks` spends one unit per block and INVOKE passes its fuel on,
  so the same fuel should work on both sides.
- `ctx_eom_bounded` is preserved because `dft_fn` only replaces `fn_blocks`;
  that needs the `fn' = dft_fn fn` conjunct, not `dft_fn_rel`.
