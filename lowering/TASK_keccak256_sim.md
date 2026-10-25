# TASK: expression simulation of keccak256

## Meta
Status: planned
Priority: P1
Created: 2026-10-25
Location: lowering/ (file lowering/exprSimBuiltinsScript.sml)

## Theorem Statement (FROZEN)

In lowering/exprSimBuiltinsScript.sml:

```sml
Theorem compile_keccak256_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann Keccak256 args)
```

The judgment (`expr_sim_below`, `expr_vv_ok`, `expr_sim_ok`, `expr_ok`, `expr_sim_pre`, `expr_sim_inv`) is in lowering/exprSimHypsScript.sml; `expr_sim`, `expr_vv_sim`, `expr_post`, `expr_val_rel`, `expr_val_at` in lowering/exprSimScript.sml.

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

Weakly frozen dependencies (use as stated; they are `cheat` in your copy, which is fine; do not edit them):
- `lower_value_word_shape` in lowering/exprSimOperatorsScript.sml (for a word-typed operand), `compile_expr_extends` in lowering/exprSimUnwrapScript.sml.

## Completion Criteria

1. `holbuild -j4 build exprSimBuiltinsTheory exprSimMainTheory` passes; no CHEAT in the theorem above or in helpers you add. Cheats inherited only through the weakly frozen dependencies are fine; don't route through any other cheated lemma.
2. Helpers in their most general form, no duplicates of existing lemmas. Put helpers in a new theory file, `lowering/exprSimHashesScript.sml` (theory `exprSimHashes`), and add it to exprSimBuiltins' `Ancestors`; in exprSimBuiltinsScript.sml change only this proof. The other builtins' lemmas stay cheated.
3. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`. Proofs under ~50 lines each; no step near the 2.5 s tactic timeout (never raise it).

**If the theorem is false as stated:** give a concrete counterexample and the tightest fix. Do NOT weaken the statement and do not add premises to `expr_sim_pre`/`expr_sim_inv`.

## Build

```
holbuild -j4 build exprSimBuiltinsTheory exprSimMainTheory
```
(run from the project root, the directory containing holproject.toml)

## Background

vyper-hol issue #636 proves that the Vyper→Venom expression lowering (`compile_expr`, lowering/defs/exprLoweringScript.sml) simulates the source interpreter (`eval_expr`, semantics/), one case lemma per expression form, by strong induction on expression size (`compile_expr_sim` in lowering/exprSimMainScript.sml calls this lemma). `keccak256(x)` lowers (`compile_builtin_dispatch_body_def`, case `Keccak256`) to `lower_value compile_expr` of the operand and then `compile_keccak256_bytes` (Bytes/String operand: the value is in memory at the operand) or `compile_keccak256_bytesm` (bytesN operand: a word), both defined in lowering/defs/builtinHashingScript.sml, under `as_stack_val`. The source is `evaluate_builtin` case `Keccak256` (semantics/vyperContextScript.sml). Typing: `well_typed_builtin_app` case `Keccak256` (semantics/type/vyperTypeSystemScript.sml).

Closest proved patterns: the one-operand composition `compile_convert_frag_sim` (exprSimConvert) and the two-operand `compile_bop_sim` (exprSimOps) for a word operand; for an operand whose value is in memory, `expr_val_rel`'s `val_in_memory` side, `expr_val_at` and `expr_val_rel_mem_agree` (exprSim). `expr_vv_ok` of a StackValue form follows from `expr_sim_ok` via `expr_ok_stack` (exprSimHyps) / `expr_vv_sim_stack` (exprSim).

## Domain Constraints

- Project rules in AGENTS.md at the project root: holbuild only, no interactive g/e sessions, `rename1` rather than generated names.
- Don't edit files under semantics/, venom/ or lowering/defs/, nor lowering/exprSimOperatorsScript.sml, exprSimLeavesScript.sml, exprSimAggregatesScript.sml, exprSimHypsScript.sml, exprSimScript.sml, or any existing theorem; add helpers in the new theory.
- Another prover run is working on other lemmas of exprSimBuiltinsScript.sml in a separate branch; keep your edits to that file to this one proof and the `Ancestors` line.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| judgment | lowering/exprSimScript.sml | expr_sim_def, expr_post_def, expr_val_rel_def, expr_val_at_def, expr_exit_def, expr_res_ok_def, expr_vv_sim_stack, expr_sim_values, expr_val_rel_mem_agree, stmt_state_rel_vars_frame |
| hypotheses | lowering/exprSimHypsScript.sml | expr_sim_pre_def, expr_sim_inv_def, expr_ok_stack, expr_ok_of_vv, expr_sim_below_mem, expr_sim_pre_eval, expr_sim_pre_builtin_arg, well_typed_expr_type_evaluates, eval_expr_builtin_value |
| one-operand pattern | lowering/exprSimConvertScript.sml | lower_value_convert, eval_expr_convert_cases, convert_frag_def, expr_post_convert, compile_convert_frag_sim |
| two-operand pattern | lowering/exprSimOpsScript.sml | eval_expr_bop_cases, binop_frag_straight, eval_operand_frame, expr_val_rel_word, local_region_frame, expr_post_bop, compile_bop_sim |
| hash run lemmas | lowering/builtinPropsScript.sml | step_SHA3, step_ALLOCA, compile_keccak256_word_correct, peel_alloca_impl_tac, weak_spec_chain_tac |
| ALLOCA / memory frame | lowering/loweringSliceScript.sml, lowering/localPtrsPropsScript.sml, lowering/loweringHaltScript.sml | stmt_state_rel_exec_alloca, alloca_inv_exec_alloca, local_ptrs_rel_exec_alloca_fresh, step_alloca_frame |
| straight_fresh / frag_exec | lowering/freshWritesScript.sml, lowering/fragExecScript.sml | straight_fresh_def, frag_exec_straight_fresh(_abort), frag_exec_then, frag_exec_weaken, frag_exec_exit_prefix, frag_exec_pre_exit_c |
| encodings | lowering/defs/valueEncodingScript.sml | typed_val_to_w256_def, val_in_memory_def, mem_word_at |
| main theorem | lowering/exprSimMainScript.sml | compile_builtin_case_sim (how this lemma is used) |
| lowering | lowering/defs/exprLoweringScript.sml, lowering/defs/builtinHashingScript.sml, lowering/defs/contextScript.sml | compile_builtin_dispatch_body_def, lower_value_def, unwrap_value_def, compile_keccak256_bytes_def, compile_keccak256_bytesm_def, compile_alloc_buffer_def |
| Venom semantics | venom/defs/venomExecSemanticsScript.sml | SHA3, MLOAD, MSTORE, ALLOCA (exec_alloca_def) |
| source | semantics/vyperContextScript.sml | evaluate_builtin_def (Keccak256), Keccak_256_w64 |
| typing | semantics/type/vyperTypeSystemScript.sml, semantics/prop/vyperTypeBuiltinsScript.sml | well_typed_builtin_app_def, value_has_type for BytesV/StringV |

## Notes

Analysis of the two lowering paths is in a comment above the hash lemmas in lowering/exprSimBuiltinsScript.sml.
