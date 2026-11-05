# TASK: ConcretizeMemLoc step contract

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: venom/passes/concretize_mem_loc/contract/concretizeStepContractScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem concretize_step_contract_at:
  o1_step_contract_at 2 rpolicy (CFP_Simple VP_ConcretizeMemLoc)
```

Supporting definitions (do not change them):
- `o1_step_contract_at_def`, `o1_fn_shape_def`, `o1_ctx_shape_def`, `fresh_names_ok_def`,
  `label_map_sources_ok_def`, `o1_fn_row_def`, `fn_pass_step_def`:
  `venom/compiler/o1PassContractScript.sml`
- `execute_configured_fn_pass_concretize` (simp rewrite): `venom/defs/venomPassDispatcherScript.sml`
- `concretize_function_fuel_in_context_def`, `apply_context_concretize_layout_def`,
  `apply_concretize_layout_def`, `concretize_function_with_positions_def`,
  `concretize_inst_with_positions_def`, `fn_has_alloca_def`:
  `venom/passes/concretize_mem_loc/defs/concretizeMemLocDefsScript.sml`
- `fn_shape_ok_def`, `call_checks_ok_def`, `calls_flagged_def`, `flag_path_def`,
  `flag_fails_def`, `revert_path_def`, `opaque_use_ok_def`, `retpc_shape_ok_def`,
  `inst_shape_ok_def`, `first_block_no_preds_def`, `copy_phi_var_def`:
  `venom/compiler/unitShapeDefsScript.sml`
- `clear_nops_function_def`: `venom/passes/shared/defs/passSharedDefsScript.sml`

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build concretizeStepContractTheory` passes with zero CHEAT warnings.
2. No duplicate or near-duplicate lemmas: search before adding a helper, reuse existing ones.
3. Edit only `venom/passes/concretize_mem_loc/**` (the target script, and new leaf
   theories next to it). Do not edit shared ancestors (`venom/compiler/`,
   `venom/defs/`, `venom/passes/shared/`, other passes). New helper theories go in
   `venom/passes/concretize_mem_loc/contract/` and must not end in `Lib`.

**If the theorem is false as stated:** produce a concrete counterexample, state the
tightest sufficient fix, and do NOT weaken the statement.

## Build

```
holbuild -j4 build concretizeStepContractTheory
```
(from the project root, the directory with `holproject.toml`). Never raise the
tactic timeout; a step over 2.5s is to be split.

## Background

This is the structural half of the O1 pass contract for the ConcretizeMemLoc pass, at
its walk position (run 2). The pass either returns its input function unchanged
(already static layout, no ALLOCA) or rewrites each ALLOCA to `ASSIGN [Lit pos]`
(same outputs and inst_id; an ALLOCA with no position becomes NOP, and all NOPs are
then cleared), and changes only metadata fields otherwise. The supply is passed
through unchanged and the label map is `[]`. The contract asks that the output keep
the observed context's per-function shape (`o1_fn_shape`), that its labels/ids come
from the input, and that it contain no ALLOCA (row 3).

## Domain Constraints

- vyper-hol AGENTS.md rules hold: no `cheat`, no interactive `g`/`e`, no
  `TRY`/`ORELSE` around `metis_tac` or other search (select goals with `>~`, `>-`,
  `>|`), proofs under ~50 lines each, `rename1` rather than generated names.
- Don't use `holbuild run` or `holbuild repl`; probe with scratch theorems built by
  `holbuild build`, and remove probes before finishing.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Target | `venom/passes/concretize_mem_loc/contract/concretizeStepContractScript.sml` | the theorem, with intuition comments |
| Concretize defs | `venom/passes/concretize_mem_loc/defs/concretizeMemLocDefsScript.sml` | the pass |
| Concretize transition facts | `venom/passes/concretize_mem_loc/proofs/concretizeMemLocTransitionProofsScript.sml` | `concretize_function_fuel_in_context_metadata_transition`, `..._invoke_targets`, `concretize_function_with_positions_removes_alloca`, local helpers on block maps |
| Concretize structural facts | `venom/passes/concretize_mem_loc/concretizeMemLocCorrectnessScript.sml` | `concretize_preserves_wf_function` (for `concretize_function amap`, via `map_transform_preserves_wf` + `clear_nops_function_preserves_wf`), `concretize_function_positions_adapter` |
| Shared pass lemmas | `venom/passes/shared/passSharedPropsScript.sml`, `venom/passes/shared/defs/passSharedDefsScript.sml`, `venom/passes/shared/` | clear_nops lemmas, map-transform preservation |
| Contract defs | `venom/compiler/o1PassContractScript.sml` | `o1_step_contract_at`, `o1_fn_shape`, `fn_pass_step` |
| Shape defs | `venom/compiler/unitShapeDefsScript.sml` | `fn_shape_ok`, `call_checks_ok`, `retpc_shape_ok`, `copy_phi_var_mono`, `reachable_fn` lemmas |
| Sibling step-contract proofs | `venom/passes/fmp_lowering/contract/` (`fmpStepContractScript.sml`, `fmpStepCallChecks*`), `venom/compiler/o1ContractSueStepScript.sml`, `venom/compiler/o1ContractCfgNormStepScript.sml`, `venom/compiler/o1ContractLowerDloadScript.sml` | how other passes discharge `o1_fn_shape` / `call_checks_ok` / `retpc_shape_ok` |
| Well-formedness | `venom/defs/venomWfScript.sml` | `inst_wf` (ALLOCA has one output, `[Lit sz]` operand), `fn_inst_wf`, `wf_function` |

Find more with `grep -rn <name> venom/`.

## Notes

The statement was checked by hand against the definitions; see the comment above the
theorem in the target script.
