# TASK: MakeSSA keeps fn_ptr_ok

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/compiler/ (theorem in o1ContractMakeSsaPtrOkScript.sml)

## Theorem Statement (FROZEN)

```sml
Theorem make_ssa_current_fn_ptr_ok:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\ fn_ptr_ok P fn ==>
  fn_ptr_ok P fn' /\ fn_ptr_ok P (reachable_fn fn')
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build o1ContractMakeSsaPtrOkTheory` passes at the default tactic timeout, and `make_ssa_current_fn_ptr_ok` is saved without a cheat.
2. The statement above is unchanged, byte for byte.
3. No duplicate or near-duplicate lemmas; search before adding a helper.

**If the theorem is false as stated:** produce a counterexample, state the tightest fix, and stop. Do NOT weaken the statement.

## Build

```
holbuild -j4 build o1ContractMakeSsaPtrOkTheory
```

## Background

Part of vyper-hol's O1 pipeline proof: MakeSSA (`make_ssa_current_fn`) must keep the pointer discipline `ptr_discipline`, whose syntactic half is `fn_ptr_ok P` of each function and of its reachable part. This theorem is that syntactic half for one function. The comment above the statement says why it should hold.

## Domain Constraints

- Put helper lemmas in `venom/compiler/o1ContractMakeSsaPtrOkScript.sml`, or in new theories next to it in `venom/compiler/`. Do not edit any other existing file.
- Treat `make_ssa_current_fn` as a black box: use the facts proved or admitted about it (Available Resources), do not unfold the pass's definition.
- `make_ssa_current_fn_origin`, `make_ssa_current_fn_wf_ssa`, `make_ssa_current_fn_phis_non_degenerate` are admitted (cheated) while other jobs prove them: use their statements as given; do not edit or prove them. The only cheats that may remain in this theorem's proof chain are inherited from those.
- No `cheat`, no new axioms, no raised tactic timeout, no `TRY`/`ORELSE` around `metis_tac` or other search: select goals with `>-`, `>~`, `>|`.
- Proofs at most ~50 lines each; split into helper lemmas. Use `rename1`, never generated names.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Target | venom/compiler/o1ContractMakeSsaPtrOkScript.sml | the theorem, with the argument in a comment |
| fn_ptr_ok | venom/compiler/ptrDisciplineScript.sml | ptr_roots, fn_pv, ptr_use_ok, fn_ptr_ok |
| Pointer closure | venom/passes/shared/defs/pointerConfinedDefsScript.sml, venom/passes/shared/proofs/pointerConfinedPropsScript.sml | pointer_derived_vars, alloca_roots, affine_pointer_ops, phi_pv_all_var; pointer_use_vars_initial/_closed/_least |
| Origin map (admitted) | venom/passes/make_ssa/proofs/makeSsaCurrentOriginScript.sml | make_ssa_current_fn_origin |
| SSA (admitted) | venom/passes/make_ssa/proofs/makeSsaCurrentWfSsaScript.sml | make_ssa_current_fn_wf_ssa |
| Output input rows | venom/passes/make_ssa/proofs/makeSsaCurrentInputOkScript.sml | make_ssa_current_fn_input_ok (all_reachable, fn_defs_reach_uses, fn_phis_cover_preds, PHI pairs are CFG edges, of fn') |
| Non-degenerate (admitted) | venom/passes/make_ssa/proofs/makeSsaCurrentNonDegenerateScript.sml | make_ssa_current_fn_phis_non_degenerate |
| CFG | venom/passes/make_ssa/proofs/makeSsaCurrentCfgScript.sml | make_ssa_current_fn_cfg, make_ssa_current_fn_all_reachable |
| Labels, metadata | venom/passes/make_ssa/proofs/makeSsaCurrentPropsScript.sml | make_ssa_current_fn_labels, make_ssa_current_fn_metadata, make_ssa_current_fn_structural |
| Well-formedness | venom/defs/venomWfScript.sml | wf_ssa, ssa_form, def_dominates_uses, phi_edge_uses_wf, phi_well_formed, fn_defs_reach_uses, def_on_all_paths, fn_phis_cover_preds, fn_phis_non_degenerate, fn_inst_wf, inst_wf |
| CFG paths | venom/defs/cfgWfScript.sml (and grep is_fn_path, fn_cfg_edge, all_reachable, fn_reachable) | paths and reachability |
| Contract rows | venom/compiler/o1PassContractScript.sml | make_ssa_input_ok, first_block_no_phi |
| Reachable part | venom/compiler/unitShapeDefsScript.sml, venom/passes/simplify_cfg/defs/simplifyCfgDefsScript.sml | reachable_fn, reachable_inst, reachable_preds, first_block_no_preds; filter_phi_ops |
| Instructions | venom/defs/venomInstScript.sml | phi_pairs, inst_output, decode_invoke, mem_write_ops/mem_read_ops (grep) |

## Notes

Paths are relative to the project root (the directory of this file).
