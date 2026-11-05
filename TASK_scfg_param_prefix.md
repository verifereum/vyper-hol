# TASK: SimplifyCFG keeps the parameter prefix

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/compiler/o1ContractSimplifyCfgParamsScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem simplify_cfg_fn_param_prefix:
  o1_fn_shape C fn /\ fn_pseudos_prefix fn /\
  EVERY (\bb. no_param_insts bb.bb_instructions) (TL fn.fn_blocks) ==>
  fn_pseudos_prefix (simplify_cfg_fn fn) /\
  EVERY (\bb. no_param_insts bb.bb_instructions)
    (TL (simplify_cfg_fn fn).fn_blocks)
```

Definitions: `simplify_cfg_fn` and the pass's steps in
`venom/passes/simplify_cfg/defs/simplifyCfgDefsScript.sml`; `o1_fn_shape`,
`first_block_no_phi` in `venom/compiler/o1PassContractScript.sml`;
`fn_pseudos_prefix`, `pseudos_prefix`, `wf_function`, `bb_well_formed` in
`venom/defs/venomWfScript.sml`; `is_pseudo`, `is_param_opcode` in
`venom/defs/venomInstScript.sml`; `no_param_insts` in
`venom/defs/callLayoutDefsScript.sml`; `subst_block_labels_fn`,
`replace_block`, `remove_block` in `venom/defs/cfgTransformScript.sml`.

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build o1ContractSimplifyCfgParamsTheory` passes with zero CHEAT warnings and zero failures.
2. The statement above is unchanged.
3. No duplicate or near-duplicate lemmas: search the `venom/passes/simplify_cfg/` theories (they already have per-step and per-round preservation machinery) before adding a helper; each helper exists once, in its most general form.
4. All new code goes in `venom/compiler/o1ContractSimplifyCfgParamsScript.sml` (new helper theories next to it in `venom/compiler/` are fine). No change to any definition or to any other existing file.

**If the theorem is false as stated:** produce a concrete counterexample, state the tightest sufficient fix, and stop. Do NOT weaken the statement.

## Build

```
holbuild -j4 build o1ContractSimplifyCfgParamsTheory
```

## Background

Part of the Vyper compiler correctness proof. The O1 pipeline's pass
contract carries a per-function row: from stage 4 on, pseudo instructions
(PHI and the parameter opcodes PARAM, FMP_PARAM, RETPC_PARAM) lead every
block and only the first block has parameters. SimplifyCFG runs at stage 5
and must keep that row. Its input also satisfies the O1 function shape
(`o1_fn_shape`), which includes `wf_function`, `first_block_no_preds` and
`first_block_no_phi`.

SimplifyCFG iterates rounds of: drop unreachable blocks, fix PHIs (filter
operands to actual predecessors, turn 1-operand PHIs into ASSIGN and
0-operand ones into NOP, sort PHIs first), a DFS that merges single-
successor/single-predecessor chains and bypasses trivial jump blocks, a
block-label substitution, and a final cleanup.

## Domain Constraints

- holbuild's per-step tactic timeout is 2.5 s; a step that exceeds it is a proof bug: split it. Never raise the timeout.
- Never wrap `metis_tac` or other search in `TRY`/`ORELSE`; select goals with `>-`, `>~`, `>|`.
- No `cheat`, no new axioms, no new definitions unless unavoidable (flag any).

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| Pass definitions | `venom/passes/simplify_cfg/defs/simplifyCfgDefsScript.sml` | rounds, collapse DFS, fixups, `collapse_dfs_ind` |
| Generic invariant lifts | `venom/passes/simplify_cfg/proofs/simplifyCfgInvariantScript.sml` | `collapse_dfs_preserves_predicate(_joint)`, per-step `*_every` lemmas, round/iter lifts |
| Structural shape | `venom/passes/simplify_cfg/proofs/simplifyCfgCollapseShapeScript.sml` | `collapse_shape`/`iteration_shape` with entry label kept at HD, per-step and per-round preservation |
| First block, wf | `venom/passes/simplify_cfg/proofs/simplifyCfgStructScript.sml` | `collapse_no_entry_preds_joint`, `simplify_cfg_round_first_block_no_preds`, `simplify_cfg_round_wf`, `collapse_property_joint` |
| wf iteration | `venom/passes/simplify_cfg/proofs/simplifyCfgWffnScript.sml` | `simplify_cfg_iter_with_labels_wf` |
| Other pass proofs | `venom/passes/simplify_cfg/proofs/` | label, PHI, shape lemmas (`fix_all_phis_entry_no_phi`, `chain_merge_entry_label`, ...) |
| Similar user | `venom/compiler/o1ContractSimplifyCfgScript.sml` | `o1_contract_simplify_cfg`, the theorem this lemma serves |
| Pseudo prefix elsewhere | `venom/compiler/o1DftStepScript.sml`, `venom/passes/fmp_lowering/contract/fmpStepContractScript.sml` | examples of proving `fn_pseudos_prefix` / TL `no_param_insts` |
| Core defs | `venom/defs/` | `venomWf`, `venomInst`, `cfgTransform`, `callLayoutDefs` |

## Notes

Intuition is in the SML comment above the theorem.
