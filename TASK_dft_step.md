# TASK: DFT's step part of the O1 pass contract

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: venom/compiler/o1DftStepScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem dft_step_contract:
  o1_step_contract rpolicy (CFP_Simple VP_DFT)
```

`o1_step_contract_def`, `o1_fn_shape_def`, `o1_ctx_shape_def`, `fresh_names_ok_def`, `label_map_sources_ok_def`, `fn_pass_step_def` are in venom/compiler/o1PassContractScript.sml. `execute_configured_fn_pass_dft` (venom/defs/venomPassDispatcherScript.sml, [simp]) says the pass's output is `dft_fn fn` with an empty label map and the supply unchanged.

**Do not modify this statement. Prove it as-is, or produce a counterexample.**

## Completion Criteria

1. `holbuild --max-heap 7000 -j4 build o1DftStepTheory` passes with zero CHEAT warnings from o1DftStepTheory and any helper theory you add.
2. No duplicate or near-duplicate lemmas.

**If the theorem is false as stated:** produce a concrete counterexample, state the tightest sufficient fix, do not weaken the statement.

## Build

```
holbuild --max-heap 7000 -j4 build o1DftStepTheory
```
(from the project root, the directory with `holproject.toml`)

## Background

The O1 pipeline runs DFT (instruction scheduling, `dft_fn`) on every function. The pass contract's step part says that on any function of the O1 shape (`o1_fn_shape` of the observed context, which does NOT include SSA), the output keeps that shape, takes no fresh labels or instruction ids, renames no label, and keeps the supply invariant. The input need not be SSA, so the existing DFT lemmas that assume `wf_ssa` (dft_fn_all_perm_of, dft_fn_dft_inv, dft_fn_blocks_well_formed, schedule_terminator_last via eda_topo_compatible) cannot be used directly; prove what's needed without SSA.

A statement checker (reading only) judged it provable. Its notes are in the comment above the theorem. Key facts: without SSA, `dft_fn` may DROP an instruction (e.g. `%x = ADD [Var "x"; Lit 1]` depends on itself, so it's never an entry and never reached), but never duplicates one. Output instructions are input ones or their `flip_operands`. The terminator stays last. `ADD [op; Label "code_end"]` is never flipped.

## Domain Constraints

- Build only with holbuild; no Holmake, no hol4-mcp, no interactive `g`/`e` sessions. Read the repo's `AGENTS.md`.
- No `cheat` in the result. Never raise the tactic timeout (2.5 s per step). No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`.
- Do not change existing definitions or proved theorems. Helpers go in this theory or new theories next to it (venom/compiler/ or venom/passes/dft/proofs/); no new axioms or hypotheses.
- Keep proofs short (≤ ~50 lines each). Use `--max-heap`, never `--maxheap`.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| DFT definition | venom/passes/dft/defs/dftDefsScript.sml | dft_fn (~630), dft_loop_step, dft_block, entry_instructions, build_eda, flip_operands, is_flippable |
| DFT structural lemmas | venom/passes/dft/proofs/dftStructuralScript.sml | dft_block_from_orig, schedule_output_from_block, dft_block_phis, dft_fn_invoke_subset, dft_fn_no_raw_fmp_ops, flip lemmas, eda_wf |
| Other DFT lemmas | venom/passes/dft/proofs/ (dftCorrectness, dftWf, dftPipelineInvar, dftTopoSort) | dft_fn_labels_map, dft_fn_entry_label, eda_deps_backward_plain, dft_fn_pseudos_prefix; check each lemma's hypotheses |
| Shape | venom/compiler/unitShapeDefsScript.sml | fn_shape_ok, inst_shape_ok, label_positions_ok, operand_case_not_label |
| Well-formedness | venom/defs/venomWfScript.sml | wf_function, bb_well_formed, fn_inst_wf, inst_wf, first_block_no_preds |
| Supply | venom/defs/irSupplyScript.sml (or grep) | ir_supply_inst_ok, fn_ir_inst_ids |
| Intuition | comment above the theorem | unchecked proof sketch |

## Notes

- Only the step part is in scope; the semantic stage part is other tasks'.
