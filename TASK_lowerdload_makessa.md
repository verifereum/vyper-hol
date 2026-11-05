# TASK: LowerDload keeps make_ssa_input_ok

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/compiler/lowerDloadMakeSsaInputScript.sml

## Theorem Statement (FROZEN)

In `venom/compiler/lowerDloadMakeSsaInputScript.sml`:

```sml
Theorem lower_dload_fn_pass_step_make_ssa_input_ok:
  fn_pass_step rpolicy (CFP_Simple VP_LowerDload) observed s fn out /\
  fn_inst_ids_distinct fn /\ fn_inst_wf fn /\ make_ssa_input_ok fn ==>
  make_ssa_input_ok out.fpo_function
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build o1ContractLowerDloadStageTheory` passes, and neither
   `lower_dload_fn_pass_step_make_ssa_input_ok` nor
   `lower_dload_stage_make_ssa_input_ok` (its consumer in
   `venom/compiler/o1ContractLowerDloadStageScript.sml`, already proved from
   it) depends on a cheat. The other `o1ContractLowerDloadStage` rows and
   ancestor theories have inherited cheats; those are expected and out of scope.
2. No duplicate or near-duplicate lemmas — each helper exists once.

**If the theorem is false as stated:** give a concrete counterexample and the
tightest sufficient fix; do NOT weaken the statement.

## Build

```
holbuild -j4 build o1ContractLowerDloadStageTheory
```

## Background

vyper-hol's O1 pipeline proof needs each pass to keep `make_ssa_input_ok`
(the input conditions of MakeSSA: all blocks reachable, definitions reach
their uses on every path, PHI well-formedness). LowerDload expands each
DLOAD into ALLOCA/ADD/CODECOPY/MLOAD and each DLOADBYTES into ADD/CODECOPY,
with fresh variables and instruction ids drawn from an IR supply; every other
instruction is kept. Intuition is in SML comments above the statement.

## Domain Constraints

- Edit only `venom/compiler/lowerDloadMakeSsaInputScript.sml`, and new
  theories named `venom/compiler/lowerDload*Script.sml` if you want to split
  helpers out. Do not edit any other file: no definition, semantics or
  shared-theory change, and do not un-`[local]` lemmas elsewhere.
  (`lower_dload_covers_member` in `o1ContractLowerDloadScript.sml` is
  `[local]`; reprove that small fact inline where you need it.)
- No `cheat`, no new axioms, no `TRY`/`ORELSE` around metis or other
  search (select goals with `>-`, `>~`, `>|`), no tactic-timeout changes.
  Each proof step must finish within holbuild's default step limit.
- Don't depend on generated variable names; use `rename1`.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Target | `venom/compiler/lowerDloadMakeSsaInputScript.sml` | the frozen theorem |
| Consumer | `venom/compiler/o1ContractLowerDloadStageScript.sml` | `lower_dload_stage_make_ssa_input_ok` uses it |
| make_ssa_input_ok, fn_pass_step, ctx_pass_stage | `venom/compiler/o1PassContractScript.sml` | definitions |
| LowerDload supply lemmas | `venom/compiler/o1ContractLowerDloadScript.sml` | `lower_dload_function_supply_cfg_edge`, `_labels`, `_reachable`, `_retained_location`, `_retained_member`, `_member`, `_reserved_output`, `lower_dload_insts_supply_append`, `lower_dload_inst_supply_preserves_vars`, `_vars`, `_control`, `_operand_provenance`, `lower_dload_blocks_supply_labels`, `_cfg` |
| LowerDload definitions | `venom/passes/lower_dload/defs/lowerDloadDefsScript.sml` | `lower_dload_inst_supply_def` … `lower_dload_function_supply_def` |
| LowerDload supply proofs | `venom/passes/lower_dload/proofs/lowerDloadSupplyProofsScript.sml` | id/supply contracts |
| Pass dispatcher | `venom/defs/venomPassDispatcherScript.sml` | `execute_configured_fn_pass_def` (VP_LowerDload case) |
| Supply coverage | `venom/defs/venomFnScheduleRunnerScript.sml` | `ir_supply_covers_unit_def`, `ir_supply_covers_fn_def`, `lookup_unique_function_def` |
| IR supply | `venom/defs/irSupplyScript.sml` | `fresh_ir_var_contract`, `inst_ir_vars_def`, `fn_ir_vars_def`, `unit_ir_vars_def` |
| Path/def predicates | `venom/defs/venomWfScript.sml` | `fn_defs_reach_uses_def`, `def_on_all_paths_def`, `is_fn_path_def`, `fn_phi_*_def`, `fn_inst_ids_distinct_def` |
| Reachability | `venom/defs/cfgWfScript.sml` | `all_reachable_def`, `fn_reachable_def` |
| Instructions | `venom/defs/venomInstScript.sml` | `phi_pairs_def`, `inst_uses_def`, `fn_insts_def`, `fn_insts_blocks_def` |
| Sibling proof of the same row | `venom/compiler/o1ContractSimplifyCfgScript.sml` | `simplify_cfg_pre_walk_make_ssa_input_ok` |
| Path-invariance pattern | `venom/compiler/o1PassContractScript.sml` | `make_ssa_input_ok_fmp_signature` (is_fn_path transfer) |

## Notes

The lemma's `fn_inst_ids_distinct fn` premise is needed: without it a block
`[d; p := 0; d]` with `d = DLOAD [Var p]` satisfies fn_defs_reach_uses (p is
defined before the second occurrence of d) but its first expansion's ADD reads
p before any definition.  `fn_inst_wf fn` is needed too: the expansion drops
a DLOADBYTES's outputs, so `[DLOADBYTES [..] -> [x]; ADD [Var x; ..] -> [y]]`
would lose x's only definition; inst_wf makes DLOADBYTES output-free.
