# TASK: LowerDload keeps the O1 step shape (supply transform)

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: venom/compiler/o1ContractLowerDloadScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem lower_dload_function_supply_wf_function:
  !s fn fn' s'.
    wf_function fn /\ ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\
    lower_dload_function_supply s fn = (fn',s') ==>
    wf_function fn'

Theorem lower_dload_function_supply_ssa_form:
  !s fn fn' s'.
    ssa_form fn /\ ir_supply_covers_fn s fn /\
    lower_dload_function_supply s fn = (fn',s') ==>
    ssa_form fn'

Theorem lower_dload_step_contract:
  o1_step_contract rpolicy (CFP_Simple VP_LowerDload)
```

**Do not modify these statements.** Prove them as-is, or produce a counterexample.
Do not modify any definition (in particular `label_positions_ok`, `o1_fn_shape`,
`fn_pass_step`, `o1_step_contract`, `lower_dload_*_supply`). Helper lemmas may go in new theories or in
`venom/compiler/o1ContractLowerDloadScript.sml` above the frozen theorems.

## Completion Criteria

1. `holbuild -j4 build venom/compiler/o1ContractLowerDloadScript.sml` passes with zero CHEAT warnings.
2. No `TRY`/`ORELSE` around `metis_tac` or other search; no tactic-timeout changes; no new axioms.
3. No duplicate helper lemmas; every proof under ~50 lines.

## Build

```
holbuild --max-heap 8000 -j4 build venom/compiler/o1ContractLowerDloadScript.sml
```
(run from the project root, the directory with holproject.toml)

## Background

vyper-hol's O1 pipeline runs Venom passes function by function. The pass-contract
theory (`venom/compiler/o1PassContractScript.sml`) asks each pass run to keep the
O1 function shape (`o1_fn_shape`), take fresh names from the IR supply
(`fresh_names_ok`) and map only its own dead labels. LowerDload
(`lower_dload_function_supply`, the transform the dispatcher runs) expands each
`DLOAD`/`DLOADBYTES` into ALLOCA/ADD/CODECOPY/MLOAD with ids and variables from the
supply. `label_positions_ok` admits `ADD [op; Label "code_end"]` for this.
The first two theorems are general facts about the transform; the third is the
step part of the contract (`o1_step_contract`: keep `o1_fn_shape`, fresh names,
label-map sources, and `ir_supply_inst_ok` of the output supply). The contract's
definitions changed since the earlier session (o1_fn_shape gained
`first_block_no_phi`, `entry_fn_no_return`, `entry_fn_no_params`; `fn_pass_step`
carries `ir_supply_covers_unit`); existing helpers may need adapting.

## Domain Constraints

- Build only with holbuild; tactic timeout is the default 2.5 s per step.
- Never wrap search tactics in TRY/ORELSE; select goals with `>~`, `>-`, `>|`.
- Avoid variable names that clash with constants (`fn` is fine in statements, but prefer `f`/`g` in new lemmas if parsing trouble arises).

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Transform | venom/passes/lower_dload/defs/lowerDloadDefsScript.sml | `lower_dload_inst_supply` ... `lower_dload_function_supply` |
| Dispatcher | venom/defs/venomPassDispatcherScript.sml | `execute_configured_fn_pass_lower_dload` [simp] |
| Supply | venom/defs/irSupplyScript.sml | `fresh_inst_id_contract`, `fresh_ir_var_contract`, `*_preserves_old`, `*_two_calls_distinct` |
| Supply coverage | venom/defs/venomFnScheduleRunnerScript.sml | `ir_supply_covers_fn`, `ir_supply_covers_unit`, `ir_supply_extends` |
| Well-formedness | venom/defs/venomWfScript.sml | `wf_function`, `bb_well_formed`, `ssa_form`, `inst_wf`, `fn_inst_wf` |
| Contract | venom/compiler/o1PassContractScript.sml | `fn_pass_step`, `o1_ctx_shape`, `o1_fn_shape`, `fresh_names_ok`, ... |
| Shape defs | venom/compiler/unitShapeDefsScript.sml | `fn_shape_ok`, `opaque_use_ok`, `gas_var`/`retpc_var` users, `label_positions_ok` |
| Similar shape-preservation proofs | venom/compiler/o1FnScheduleDecompHelpersScript.sml, venom/passes/lower_dload/proofs/lowerDloadSupplyProofsScript.sml | existing lemmas about the supply transform (freshness, ids) |
| Built theories | .holbuild/obj/ (sig files) | search with DB.find via holbuild run if needed |

## Notes

- `lowerDloadSupplyProofsScript.sml` already proves freshness facts about the supply transform; reuse them where they fit.
