# TASK: CFG normalization (supply variant): function bisimulation and frame simulation

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: venom/compiler/o1ContractCfgNormScript.sml (project root: this directory)

## Theorem Statement (FROZEN)

The two cheated theorems in `venom/compiler/o1ContractCfgNormScript.sml`:

```sml
Theorem cfg_norm_function_supply_fn_bisim:
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ first_block_no_preds fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  cfg_norm_function_supply s fn = (fn',s') ==>
  fn_bisim fn fn'

Theorem cfg_norm_function_supply_frame_sim:
  ctx_bisim C C' /\
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ first_block_no_preds fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  cfg_norm_function_supply s fn = (fn',s') ==>
  frame_sim C C' fn fn'
```

`fn_bisim`, `ctx_bisim`, `frame_sim` and their helpers are defined in `venom/compiler/o1PassLiftScript.sml`. Its cheated theorems are being proved in a separate run; you may use them as they are.

**Do not modify these statements, `cfgNormDefsScript.sml`, or anything in `o1PassLiftScript.sml`.** Prove them as-is, or produce a counterexample.

## Completion Criteria

1. The build below passes with zero CHEAT warnings in `o1ContractCfgNormTheory` (cheats inherited from `o1PassLiftTheory` are expected and fine).
2. Helper lemmas go in a new theory `venom/passes/cfg_normalization/proofs/cfgNormSupplySimScript.sml` (general facts about the supply variant) or in `o1ContractCfgNormScript.sml`; each exists once in its most general form.
3. No change to existing theories other than `o1ContractCfgNormScript.sml`.

**If a theorem is false as stated:** produce a HOL4 counterexample (EVAL on concrete values), state the tightest sufficient fix, and do NOT weaken the statement.

## Build

```
holbuild --max-heap 8000 -j4 build o1ContractCfgNormTheory
```

Run from this directory (the one with `holproject.toml`).

## Background

The O1 pipeline runs the supply variant of CFG normalization (`cfg_norm_function_supply`): each critical edge p -> t gets a fresh split block that copies, with `ASSIGN`s into fresh supply variables, the PHI values t reads along that edge, then jumps to t; p's terminator is redirected to the split block, and t's PHIs name the split block and the forwarded variables. A self-loop critical edge (p = t) is handled by updating the PHIs of the redirected block. A run of the output takes one extra block per split edge taken and otherwise matches the input's run, so runs correspond with different fuel. These theorems are the per-function facts the pass contract needs: terminating runs correspond in both directions (`fn_bisim`), and every state the output's frame reaches corresponds to one the input's frame reaches with the same alloca frame and memory ranges (`frame_sim`).

Why `wf_ssa`: a split block forwards every PHI value for its edge, duplicates included, whereas `resolve_phi` reads only the first; `def_dominates_uses` (inside `wf_ssa`) makes every PHI value available at the end of its predecessor, and `phi_edge_uses_wf` makes PHI labels distinct and equal to the predecessors.

An older variant (`cfg_norm_function`/`insert_split`, `cfgNormProof`, `cfgNormSim`) has a proof under different premises (it assumes no self-loop critical edges); its block-level lemmas may be adaptable.

## Domain Constraints

- Use holbuild only (no Holmake, no REPL sessions).
- No `cheat` in the result. No `TRY`/`ORELSE` around metis or other search. Never raise the tactic timeout.
- No `let` in theorem statements. Prefer existing lemmas to re-proving them.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Pass definitions | `venom/passes/cfg_normalization/defs/cfgNormDefsScript.sml` | supply variant: build_split_block_supply, insert_split_supply, find_and_split_supply, cfg_norm_function_supply |
| Supply lemmas | `venom/passes/cfg_normalization/proofs/cfgNormSupplyProofsScript.sml` | freshness, labels, inst ids, decl vars, invoke labels of the supply variant |
| Legacy proof | `venom/passes/cfg_normalization/proofs/cfgNormSimScript.sml`, `cfgNormProofScript.sml`, `cfgNormBaseScript.sml`, `cfgNormIterScript.sml`, `prevBbIndepScript.sml` | simulation of the name-based variant |
| Lift | `venom/compiler/o1PassLiftScript.sml` | fn_bisim, ctx_bisim, frame_reach, mem_corr, call_corr, frame_sim, ctx_bisim_step_inst |
| Supply | `venom/defs/irSupplyScript.sml`, `venom/defs/venomFnScheduleRunnerScript.sml` | fresh_ir_var, fresh_label, ir_supply_covers_fn |
| Well-formedness | `venom/defs/venomWfScript.sml` | wf_ssa, def_dominates_uses, phi_edge_uses_wf, def_available_at, fn_inst_wf, wf_function |
| Shape | `venom/compiler/unitShapeDefsScript.sml` | first_block_no_preds |
| Definedness from dominance | `venom/passes/sccp/proofs/sccpCorrectnessProofsScript.sml` (strict_dom_vars_defined_*) | existing runtime-definedness argument |
| Semantics | `venom/defs/venomExecSemanticsScript.sml` | run_defs, eval_phis, resolve_phi; `venom/defs/stateFrameScript.sml`: execution_frame |
| Exec props | `venom/props/venomExecPropsScript.sml`, `venom/simulation/crossBlockSimPropsScript.sml` | fuel monotonicity, determinism |
| Memory ranges | `venom/compiler/unitMemInvScript.sml` | inst_mem_ranges |
| Reachability | `venom/codegen/proofs/contextRawReachableScript.sml` | enters_block, active_inst |

## Notes

- See the SML comments in `o1ContractCfgNormScript.sml`.
