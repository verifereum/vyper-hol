# TASK: Algebraic opt preserves function semantics

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: venom/passes/algebraic_opt/proofs/algebraicOptProofsScript.sml

## Theorem Statement (FROZEN)

Theorem `ao_transform_function_correct_proof` in `venom/passes/algebraic_opt/proofs/algebraicOptProofsScript.sml`:

```sml
  !fuel ctx fn s sup fn' sup'.
    wf_function fn /\
    wf_ssa fn /\
    fn_inst_wf fn /\
    EVERY label_positions_ok (fn_insts fn) /\
    ir_supply_inst_ok sup /\
    ir_supply_covers_fn sup fn /\
    ao_transform_function_supply sup fn = (fn', sup') /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = NONE /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
       lookup_var x s = NONE) ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result
      (state_equiv (set sup'.irs_used_vars DIFF set sup.irs_used_vars))
      (execution_equiv UNIV)
      (execution_equiv UNIV)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx fn' s)
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `timeout 3600 holbuild -j4 build algebraicOptProofsTheory` passes with no CHEAT for `ao_transform_function_correct_proof` or anything it uses, at the default tactic timeout.
2. No duplicate or near-duplicate lemmas; each helper exists once in its most general form.
3. The definitions in `venom/passes/algebraic_opt/defs/algebraicOptDefsScript.sml` and every other existing definition are unchanged.

**If the theorem is false as stated:**
- Produce a HOL4 counterexample (e.g., `EVAL_TAC` on concrete values).
- State the tightest sufficient fix.
- Do NOT silently weaken the statement.

## Build

```
timeout 3600 holbuild -j4 build algebraicOptProofsTheory
```

## Background

The pass is Vyper's Venom AlgebraicOptimization (peephole rewrites using the DFG and variable range analysis, iszero-chain shortening, a comparator flip post-pass). The theorem says that running the function from its entry before and after the pass gives the same frame at every exit, unless the original run errors. Variable values may differ on exit: truthy-only ORs become `ASSIGN 1`, and flipped comparators change their output while keeping its truthiness. The public wrapper is `ao_transform_function_correct` in `venom/passes/algebraic_opt/algebraicOptCorrectnessScript.sml`, proved by `ACCEPT_TAC ao_transform_function_correct_proof`.

## Domain Constraints

- holbuild only. Never raise the tactic timeout (default 2.5 s per step); a step that runs over is split or given a smaller rewrite set.
- No `TRY`/`ORELSE` around `metis_tac` or any other search; select goals with `>~`, `>-`, `>|`.
- No `let` in new theorem statements. No new axioms. Don't change existing definitions or proved statements.
- Helper lemmas go in new or existing theories under `venom/passes/algebraic_opt/proofs/`; generic facts about a shared definition may go in that definition's props theory.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Pass definitions | `venom/passes/algebraic_opt/defs/algebraicOptDefsScript.sml` | `ao_transform_function_supply` and everything it calls (supply section near the end) |
| Fresh supply | `venom/defs/irSupplyScript.sml` | `fresh_inst_id`, `fresh_ir_var`, `ir_supply_inst_ok`, their contracts |
| Supply coverage | `venom/defs/venomFnScheduleRunnerScript.sml` | `ir_supply_covers_fn`, `fn_ir_vars`, `inst_ir_vars` |
| Well-formedness | `venom/defs/venomWfScript.sml` | `wf_function`, `ssa_form`, `wf_ssa`, `inst_wf`, `fn_inst_wf`, `bb_well_formed`, `fn_succs_closed` |
| Label positions | `venom/compiler/unitShapeDefsScript.sml` | `label_positions_ok` |
| Instructions | `venom/defs/venomInstScript.sml` | `get_successors`, `is_terminator`, `fn_insts` |
| Supply-threaded precedent | `venom/passes/single_use_expansion/defs/singleUseExpansionDefsScript.sml`, `venom/passes/single_use_expansion/proofs/singleUseExpansionSupplyProofsScript.sml` | Another pass that draws ids/vars from the supply, with its wf/ssa proofs |
| DFG | `venom/analysis/dfg/` | `dfg_build_function`, `dfg_get_uses`, props in `dfgAnalysisPropsScript.sml` |
| Semantics | `venom/defs/venomExecSemanticsScript.sml`, `venom/defs/venomStateScript.sml` | `run_blocks`, `exec_block`, `step_inst`, `eval_operand` |
| Equivalences | `venom/defs/stateEquivScript.sml`, `venom/props/stateEquivPropsScript.sml`, `venom/props/execEquivPropsScript.sml` | `state_equiv`, `execution_equiv`, `lift_result` and their lemmas |
| Range analysis | `venom/analysis/variable_range/` | `range_analyze`, `range_branch_refine`; proved `range_analyze_block_sound`, `range_get_range_sound` in `variableRangeAnalysisPropsScript.sml` |
| Instruction lemmas | `venom/props/venomExecPropsScript.sml`, `venom/props/venomInstPropsScript.sml` | step/exec lemmas |
| Simulation precedent | `venom/passes/assert_combiner/` | `ac_transform_function_correct` uses the same `lift_result (state_equiv F) (execution_equiv UNIV) (execution_equiv UNIV)` shape |

## Notes

The ids and variables the pass takes from the supply are above every id in `fn` and outside `fn`'s variables, by `ir_supply_inst_ok` and `ir_supply_covers_fn`.
