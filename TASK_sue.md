# TASK: Single-use expansion (supply variant): function bisimulation and frame simulation

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: venom/compiler/o1ContractSueScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

The two cheated theorems in `venom/compiler/o1ContractSueScript.sml`:

```sml
Theorem sue_expand_function_supply_fn_bisim:
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\
  EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  sue_expand_function_supply s fn = (fn',s') ==>
  fn_bisim fn fn'

Theorem sue_expand_function_supply_frame_sim:
  ctx_bisim C C' /\
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\
  EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts fn) /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  sue_expand_function_supply s fn = (fn',s') ==>
  frame_sim C C' fn fn'
```

`fn_bisim`, `ctx_bisim`, `frame_sim` and their helpers are defined in `venom/compiler/o1PassLiftScript.sml`. Its cheated theorems (`ctx_bisim_step_inst` etc.) are being proved in a separate run; you may use them as they are.

**Do not modify these statements, or anything in `o1PassLiftScript.sml`.** Prove them as-is, or produce a counterexample.

## Completion Criteria

1. The build below passes with zero CHEAT warnings in `o1ContractSueTheory` (cheats inherited from `o1PassLiftTheory` are expected and fine).
2. Helper lemmas go in a new theory `venom/passes/single_use_expansion/proofs/singleUseExpansionSupplySimScript.sml` (general facts about the supply variant) or in `o1ContractSueScript.sml`; each exists once in its most general form.
3. No change to existing theories other than `o1ContractSueScript.sml`.

**If a theorem is false as stated:** produce a HOL4 counterexample (EVAL on concrete values), state the tightest sufficient fix, and do NOT weaken the statement.

## Build

```
holbuild --max-heap 8000 -j4 build o1ContractSueTheory
```

Run from this directory (the one with `holproject.toml`).

## Background

The O1 pipeline runs the supply variant of single-use expansion (`sue_expand_function_supply`): before an instruction, each operand that is a literal or a multiply-used variable is copied by an `ASSIGN` into a fresh variable from the IR name supply, and the instruction reads the copy. PHIs, params, ASSIGN and OFFSET are skipped. These two theorems are the per-function facts the pass contract needs: runs correspond in both directions (`fn_bisim`), and every state the expanded function reaches corresponds to one the original reaches with the same alloca frame and memory ranges (`frame_sim`). An older, name-based variant (`sue_expand_function`) has a same-fuel proof with different premises; its instruction-level lemmas may be adaptable.

## Domain Constraints

- Use holbuild only (no Holmake, no REPL sessions).
- No `cheat` in the result. No `TRY`/`ORELSE` around metis or other search. Never raise the tactic timeout.
- No `let` in theorem statements. Prefer existing lemmas to re-proving them.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Pass definitions | `venom/passes/single_use_expansion/defs/singleUseExpansionDefsScript.sml` | supply variant at the end; sue_needs_assign, sue_should_skip |
| Supply lemmas | `venom/passes/single_use_expansion/proofs/singleUseExpansionSupplyProofsScript.sml` | freshness (sue_alloc_assign_supply_contract, *_supply_extends, *_supply_covered), structure |
| Legacy proof | `venom/passes/single_use_expansion/proofs/singleUseExpansionProofsScript.sml`, `venom/passes/single_use_expansion/singleUseExpansionCorrectnessScript.sml` | same-fuel proof of the name-based variant (sue_inst_sim_at, sue_block_sim_induct) |
| Lift | `venom/compiler/o1PassLiftScript.sml` | fn_bisim, ctx_bisim, frame_reach, mem_corr, call_corr, frame_sim, ctx_bisim_step_inst |
| Supply | `venom/defs/irSupplyScript.sml`, `venom/defs/venomFnScheduleRunnerScript.sml` | fresh_ir_var, fresh_inst_id, ir_supply_covers_fn, fn_ir_vars |
| Well-formedness | `venom/defs/venomWfScript.sml` | wf_ssa, def_dominates_uses, def_available_at, fn_inst_wf, wf_function |
| Definedness from dominance | `venom/passes/sccp/proofs/sccpCorrectnessProofsScript.sml` (strict_dom_vars_defined_*), `venom/passes/remove_unused/proofs/removeUnusedSsaProofsScript.sml` | existing runtime-definedness arguments |
| Semantics | `venom/defs/venomExecSemanticsScript.sml` | run_defs, step_inst_base, eval_phis; `venom/defs/stateFrameScript.sml`: execution_frame |
| Exec props | `venom/props/venomExecPropsScript.sml`, `venom/simulation/crossBlockSimPropsScript.sml` | fuel monotonicity, determinism |
| Memory ranges | `venom/compiler/unitMemInvScript.sml` | inst_mem_ranges |
| Reachability | `venom/codegen/proofs/contextRawReachableScript.sml` | enters_block, active_inst |

## Notes

- See the SML comments in `o1ContractSueScript.sml`.
