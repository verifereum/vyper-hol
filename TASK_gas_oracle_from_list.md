# TASK: list run to oracle run (gas_oracle_from_list)

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/compiler

## Theorem Statement (FROZEN)

In `venom/compiler/dftGasOracleFromListScript.sml`:

```sml
Theorem gas_oracle_from_list:
  EVERY wf_function ctx.ctx_functions /\
  EVERY (\fn. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
                fn.fn_blocks) ctx.ctx_functions ==>
  ?orc. FINITE {e | orc e <> 0w} /\
      (!fuel. gas_res_rel (run_context fuel ctx s) (ev_context orc fuel ctx s)) /\
      (!fn inst t. raw_reachable s ctx fn inst t ==>
         ?p d. ev_reachable orc s ctx p d fn inst
                 (t with vs_gas_readings := s.vs_gas_readings))
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

The definitions in `venom/compiler/dftGasOracleDefsScript.sml` are frozen too: don't edit that file.

## Completion Criteria

1. `holbuild -j4 build dftGasOracleFromListTheory` passes from the project root at the default tactic timeout.
2. `venom/compiler/dftGasOracleFromListScript.sml` has no `cheat`, and its theory's build log (`.holbuild/logs/current/vyper-hol/dftGasOracleFromListTheory/build.log`) has no CHEAT warning for a theorem of that file.
3. No duplicate or near-duplicate lemmas; each helper exists once, in its most general form.

**If the theorem is false as stated:** give a HOL4 counterexample (EVAL on concrete values in a scratch theory), state the tightest sufficient fix, and don't weaken the statement.

## Build

```
holbuild -j4 build dftGasOracleFromListTheory
```

## Background

Venom's GAS instruction pops the next word of the state's vs_gas_readings list (an exhausted list reads 0w); INVOKE threads the list through the callee. The oracle semantics in dftGasOracleDefs instead reads GAS from a function of the event, where an event names a GAS execution by place: the frame path of INVOKE sites (block depth, INVOKE id), the block depth along the call chain, and the GAS id. This theorem says every list run is an oracle run: one oracle, with finitely many nonzero words, matches the list run at every fuel (results equal up to vs_gas_readings, gas_res_rel) and every raw_reachable state. It is one of four pieces of a DFT (instruction scheduling) correctness proof: DFT reorders GAS reads, and event names don't depend on the order.

## Domain Constraints

- holbuild only, at most `-j4`. Never raise the tactic timeout, never pass `--skip-checkpoints`, never wrap metis or other search in `TRY` or `ORELSE`.
- Don't edit any existing theory. Put helpers in new theories under `venom/compiler/` whose names start with `dftGasFromList` (other provers work on sibling pieces at the same time and use other prefixes), and keep each under about 500 lines.
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

The statement was checked against the definitions by a reviewer, who found it true: names are unique within one run given distinct ids per block (depth strictly increases within a frame; the call site is part of the callee's frame), and runs at different fuels are prefixes of one another. A sibling piece (gas_oracle_to_list, the converse) is being proved at the same time on another branch.
