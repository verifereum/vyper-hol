# TASK: oracle run to list run (gas_oracle_to_list)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/compiler

## Theorem Statement (FROZEN)

In `venom/compiler/dftGasOracleToListScript.sml`:

```sml
Theorem gas_oracle_to_list:
  EVERY wf_function ctx.ctx_functions /\ FINITE {e | orc e <> 0w} ==>
  ?W. (!fuel. gas_res_rel (run_context fuel ctx (s with vs_gas_readings := W))
                          (ev_context orc fuel ctx s)) /\
      (!p d fn inst t. ev_reachable orc s ctx p d fn inst t ==>
         ?ws. raw_reachable (s with vs_gas_readings := W) ctx fn inst
                (t with vs_gas_readings := ws))
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

The definitions in `venom/compiler/dftGasOracleDefsScript.sml` are frozen too: don't edit that file.

## Completion Criteria

1. `holbuild -j4 build dftGasOracleToListTheory` passes from the project root at the default tactic timeout.
2. `venom/compiler/dftGasOracleToListScript.sml` has no `cheat`, and its theory's build log (`.holbuild/logs/current/vyper-hol/dftGasOracleToListTheory/build.log`) has no CHEAT warning for a theorem of that file.
3. No duplicate or near-duplicate lemmas; each helper exists once, in its most general form.

**If the theorem is false as stated:** give a HOL4 counterexample (EVAL on concrete values in a scratch theory), state the tightest sufficient fix, and don't weaken the statement.

## Build

```
holbuild -j4 build dftGasOracleToListTheory
```

## Background

Venom's GAS instruction pops the next word of the state's vs_gas_readings list (an exhausted list reads 0w); INVOKE threads the list through the callee. The oracle semantics in dftGasOracleDefs instead reads GAS from a function of the event, where an event names a GAS execution by place: the frame path of INVOKE sites (block depth, INVOKE id), the block depth along the call chain, and the GAS id. This theorem says every oracle run whose oracle has finitely many nonzero words is a list run: one reading list W, given to the initial state, matches the oracle run at every fuel (results equal up to vs_gas_readings, gas_res_rel) and every ev_reachable state. It is one of four pieces of a DFT (instruction scheduling) correctness proof.

## Domain Constraints

- holbuild only, at most `-j4`. Never raise the tactic timeout, never pass `--skip-checkpoints`, never wrap metis or other search in `TRY` or `ORELSE`.
- Don't edit any existing theory. Put helpers in new theories under `venom/compiler/` whose names start with `dftGasToList` (other provers work on sibling pieces at the same time and use other prefixes), and keep each under about 500 lines.
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

## Notes

The statement was checked against the definitions by a reviewer, who found it true: a run that never terminates can meet infinitely many events, but finitely many nonzero ones, after the last of which the exhausted list's 0w agrees with the oracle; event names need not be distinct here. A sibling piece (gas_oracle_from_list, the converse) is being proved at the same time on another branch.
