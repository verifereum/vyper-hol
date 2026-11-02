# TASK: Single-use expansion as O1 stage 6: step contract and stage contract

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: venom/compiler/ (project root: this directory)

## Theorem Statement (FROZEN)

Four cheated theorems:

`venom/compiler/o1ContractSueStepScript.sml`:
```sml
Theorem sue_step_contract:
  o1_step_contract rpolicy (CFP_Simple VP_SingleUseExpansion)
```

`venom/compiler/o1ContractSueScript.sml` (end of file):
```sml
Theorem sue_expand_function_supply_used_inst_ids:
  FST (sue_expand_function_supply (s with irs_used_inst_ids := ids) fn) =
  FST (sue_expand_function_supply s fn)

Theorem sue_stage_walk:
  o1_run_contract rpolicy 6
```

`venom/compiler/o1ContractSimplifyCfgScript.sml`:
```sml
Theorem simplify_cfg_fn_no_alloca:
  EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts fn) ==>
  EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts (simplify_cfg_fn fn))
```

Do not modify these statements. Prove them as-is, or produce a counterexample.
Do not modify any definition, `o1PassContractScript.sml`, `o1PassLiftScript.sml`,
or the already-proved theorems `sue_expand_function_supply_fn_bisim` and
`sue_expand_function_supply_frame_sim`.

## Completion Criteria

1. The build below passes with zero CHEAT warnings in `o1ContractSueStepTheory`,
   `o1ContractSueTheory` and `o1ContractSimplifyCfgTheory` (cheats inherited
   from other ancestors are expected and fine).
2. Helper lemmas about the supply variant of SUE go in
   `venom/passes/single_use_expansion/proofs/singleUseExpansionSupplyProofsScript.sml`
   or `singleUseExpansionSupplySimScript.sml`; lemmas about `simplify_cfg_fn`
   next to the existing no-raw-fmp chain in
   `venom/passes/simplify_cfg/proofs/simplifyCfgLabelPropsScript.sml` (or a new
   theory under that directory); contract-level lemmas in the three files above.
   Each exists once in its most general form.
3. No change to existing theorem statements.

If a theorem is false as stated: produce a HOL4 counterexample (EVAL on concrete
values), state the tightest sufficient fix, and do NOT weaken the statement.

## Build

```
holbuild --max-heap 8000 -j4 build o1ContractTheoremsTheory o1PipelineCorrectTheory
```

Run from this directory (the one with `holproject.toml`).

## Background

The O1 pipeline is a walk of function passes (`o1_fn_passes`); between runs a
row invariant `o1_inv k` holds. SingleUseExpansion is run 6: it maps row 6
(`o1_ssa_inv`: the lowered-memory invariant, no ALLOCA, plus `wf_ssa` of every
function) to row 7 (`o1_lowered_inv`). The pass is `sue_expand_function_supply`:
before an instruction, each literal or multiply-used variable operand is copied
by an `ASSIGN` into a fresh variable from the IR supply.

The per-function semantic facts are proved: `sue_expand_function_supply_fn_bisim`
and `sue_expand_function_supply_frame_sim` in `o1ContractSueScript.sml`. One of
their premises is `ir_supply_inst_ok s`, which `ctx_pass_stage`/`fn_pass_step`
don't provide. `fresh_inst_id` reads only `irs_next_inst`, so the expanded
function is the same from `s with irs_used_inst_ids := ids` for any `ids`
(`sue_expand_function_supply_used_inst_ids`); the stage proof can replay the
step from such a supply.

`sue_step_contract` is the syntactic side: the output keeps `o1_fn_shape`,
names are fresh, the label map is sound, and `ir_supply_inst_ok` is kept.

`simplify_cfg_fn_no_alloca` is needed by run 5's contract (already proved
modulo this lemma in `simplify_cfg_stage_walk`). The no-raw-fmp chain in
`simplifyCfgLabelPropsScript.sml` (around lines 2559–3130, public
`simplify_cfg_fn_with_labels_no_raw_fmp_ops`) proves the same kind of fact for
another opcode property.

## Domain Constraints

- Use holbuild only (no Holmake, no REPL sessions).
- No `cheat` in the result. No `TRY`/`ORELSE` around metis or other search.
  Never raise the tactic timeout.
- No `let` in theorem statements. Prefer existing lemmas to re-proving them.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Template | `venom/compiler/o1ContractSimplifyCfgScript.sml`, `o1ContractSimplifyCfgStepScript.sml` | the proved run-5 contract: stage_functions, eom_bounded, bisim, sim, mem_inv, stage_walk, step contract |
| Contract defs | `venom/compiler/o1PassContractScript.sml` | o1_step_contract, o1_run_contract, o1_stage_contract, o1_inv, o1_fn_shape, fresh_names_ok, label_map_sources_ok |
| Lift | `venom/compiler/o1PassLiftScript.sml` | fn_bisim, ctx_bisim, frame_sim, lifting lemmas |
| SUE defs | `venom/passes/single_use_expansion/defs/singleUseExpansionDefsScript.sml` | supply variant at the end |
| SUE supply lemmas | `venom/passes/single_use_expansion/proofs/singleUseExpansionSupplyProofsScript.sml` | freshness, *_supply_extends, *_supply_covered, structure |
| SUE sim | `venom/passes/single_use_expansion/proofs/singleUseExpansionSupplySimScript.sml` | per-function simulation helpers |
| Supply | `venom/defs/irSupplyScript.sml`, `venom/defs/venomFnScheduleRunnerScript.sml` | fresh_ir_var, fresh_inst_id, ir_supply_inst_ok, ir_supply_covers_fn |
| Dispatcher | `venom/defs/venomPassDispatcherScript.sml` and `venomPassDispatcherProps` | how CFP_Simple VP_SingleUseExpansion runs |
| SimplifyCFG | `venom/passes/simplify_cfg/` | simplify_cfg_fn, label props (no-raw-fmp chain) |

## Notes

- See the SML comments next to the statements.
