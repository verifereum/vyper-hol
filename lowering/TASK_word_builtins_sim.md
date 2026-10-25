# TASK: expression simulation of the word builtins (as_wei_value, floor, addmod, mulmod, pow_mod256)

## Meta
Status: planned
Priority: P1
Created: 2026-10-25
Location: lowering/ (file lowering/exprSimBuiltinsScript.sml)

## Theorem Statement (FROZEN)

In lowering/exprSimBuiltinsScript.sml:

```sml
Theorem compile_as_wei_value_sim:
  !cenv ann d args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann (AsWeiValue d) args)

Theorem compile_floor_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann Floor args)

Theorem compile_addmod_sim:
  !cenv ann args.
    ~names_builtin AddMod args ==>
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann AddMod args)

Theorem compile_mulmod_sim:
  !cenv ann args.
    ~names_builtin MulMod args ==>
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann MulMod args)

Theorem compile_pow_mod256_sim:
  !cenv ann args.
    ~names_builtin PowMod256 args ==>
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann PowMod256 args)

Theorem compile_addmod_names_sim:
  !cenv ann aty a bty b mty m.
    expr_vv_ok cenv (Builtin ann AddMod [Name aty a; Name bty b; Name mty m])

Theorem compile_mulmod_names_sim:
  !cenv ann aty a bty b mty m.
    expr_vv_ok cenv (Builtin ann MulMod [Name aty a; Name bty b; Name mty m])

Theorem compile_powmod256_names_sim:
  !cenv ann aty a bty b.
    expr_vv_ok cenv (Builtin ann PowMod256 [Name aty a; Name bty b])
```

The judgment (`expr_sim_below`, `expr_vv_ok`, `expr_sim_ok`, `expr_ok`, `expr_sim_pre`, `expr_sim_inv`, `names_builtin`) is in lowering/exprSimHypsScript.sml; `expr_sim`, `expr_vv_sim`, `expr_post`, `expr_val_rel` in lowering/exprSimScript.sml.

**Do not modify these statements.** Prove them as-is, or produce a counterexample.

Weakly frozen dependencies (use as stated; they are `cheat` in your copy, which is fine; do not edit them):
- `lower_value_word_shape` and `compile_binop_shape` in lowering/exprSimOperatorsScript.sml.

## Completion Criteria

1. `holbuild -j4 build exprSimBuiltinsTheory exprSimMainTheory` passes; no CHEAT in the eight theorems above or in helpers you add. Cheats they inherit only through `lower_value_word_shape`/`compile_binop_shape` are fine; don't route through any other cheated lemma (e.g. exprSimLeaves' `compile_name_sim` rests on the cheated `compile_name_other_sim`; exprSim's proved `compile_name_word_sim` is the route for word locals).
2. Helpers in their most general form, no duplicates of existing lemmas. Put helpers in a new theory file, `lowering/exprSimWordBuiltinsScript.sml` (theory `exprSimWordBuiltins`), and add it to exprSimBuiltins' `Ancestors`; keep exprSimBuiltinsScript.sml to the eight proofs. Other builtins' lemmas (keccak256, ceil, ...) stay cheated.
3. No `TRY`/`ORELSE` around `metis_tac` or other search; select goals with `>~`, `>-`, `>|`. Proofs under ~50 lines each; no step near the 2.5 s tactic timeout (never raise it).

**If a theorem is false as stated:** give a concrete counterexample and the tightest fix. Do NOT weaken the statement and do not add premises to `expr_sim_pre`/`expr_sim_inv`.

## Build

```
holbuild -j4 build exprSimBuiltinsTheory exprSimMainTheory
```
(run from the project root, the directory containing holproject.toml)

## Background

vyper-hol issue #636 proves that the Vyper→Venom expression lowering (`compile_expr`, lowering/defs/exprLoweringScript.sml) simulates the source interpreter (`eval_expr`, semantics/), one case lemma per expression form, by strong induction on expression size (`compile_expr_sim` in lowering/exprSimMainScript.sml calls these lemmas). The eight lemmas here are the builtins whose operands and result are words: the lowering evaluates each operand with `lower_value compile_expr` and then emits a short straight-line sequence (`compile_builtin_dispatch_body_def` cases `AsWeiValue`, `Floor`, `AddMod`, `MulMod`, `PowMod256`, and `compile_addmod_names_def`/`compile_mulmod_names_def`/`compile_powmod256_names_def`, which `compile_expr_body_def` uses directly when the operands are all names). The source side is `evaluate_builtin` (semantics/vyperContextScript.sml) and `evaluate_as_wei_value` (semantics/vyperValueOperationScript.sml). Typing: `well_typed_builtin_app` in semantics/type/vyperTypeSystemScript.sml.

These are the same shape as the binary operators, which are proved: `compile_bop_word_sim`/`compile_bop_ok` (exprSimOperators) build on `compile_bop_sim` (exprSimOps), the two-operand composition, and `binop_frag`/`binop_frag_straight` for the operator's straight-line fragment; `compile_convert_frag_sim` (exprSimConvert) is the one-operand composition for `convert`. `expr_vv_ok` of a StackValue form follows from `expr_sim_ok` via `expr_ok_stack` (exprSimHyps) / `expr_vv_sim_stack` (exprSim).

## Domain Constraints

- Project rules in AGENTS.md at the project root: holbuild only, no interactive g/e sessions, `rename1` rather than generated names.
- Don't edit files under semantics/, venom/ or lowering/defs/, nor lowering/exprSimOperatorsScript.sml, exprSimLeavesScript.sml, exprSimAggregatesScript.sml, exprSimHypsScript.sml, exprSimScript.sml, or any existing theorem; add helpers in the new theory.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| judgment | lowering/exprSimScript.sml | expr_sim_def, expr_post_def, expr_val_rel_def, expr_val_at_def, expr_exit_def, expr_res_ok_def, expr_vv_sim_stack, expr_sim_values, compile_name_word_sim, expr_val_rel_mem_agree |
| hypotheses | lowering/exprSimHypsScript.sml | expr_sim_pre_def, expr_sim_inv_def, expr_ok_stack, expr_ok_of_vv, expr_sim_below_mem, expr_sim_pre_word_result, expr_sim_pre_builtin_arg, well_typed_expr_type_evaluates, eval_expr_builtin_value, word_value_type_def |
| two-operand pattern | lowering/exprSimOpsScript.sml | bop_result_def, binop_frag_def, eval_expr_bop_cases, binop_frag_straight, eval_operand_frame, expr_val_rel_word, local_region_frame, expr_post_bop, compile_bop_sim |
| operator case lemmas | lowering/exprSimOperatorsScript.sml | compile_bop_word_sim, compile_bop_case_sim, compile_bop_stack, compile_bop_ok, expr_sim_pre_bop, word_value_type_word, lower_value_word_shape, compile_binop_shape |
| one-operand pattern | lowering/exprSimConvertScript.sml | lower_value_convert, eval_expr_convert_cases, convert_frag_def, expr_post_convert, compile_convert_frag_sim, straight_fresh_convert (sf_step tactic), compile_convert_word_sim |
| straight-line runs, arithmetic | lowering/exprSimArithScript.sml, lowering/exprSimCompareScript.sml | compile_checked_sim, compile_safe_mul_run, compile_divmod_sim, compile_decimal_mul_div_sim, straight_fresh_* helpers, w2i/i2w and in_type_range lemmas |
| straight_fresh / frag_exec | lowering/freshWritesScript.sml, lowering/fragExecScript.sml | straight_fresh_def, straight_fresh_bind/emit_op/emit_void, frag_exec_straight_fresh(_abort), frag_exec_then, frag_exec_weaken, frag_exec_exit_prefix, frag_exec_pre_exit_c |
| main theorem | lowering/exprSimMainScript.sml | compile_builtin_case_sim, compile_names_builtin_sim (how these lemmas are used) |
| lowering | lowering/defs/exprLoweringScript.sml, lowering/defs/builtinMiscScript.sml, lowering/defs/builtinMathScript.sml | compile_builtin_dispatch_body_def, compile_expr_body_def, compile_addmod_names_def, ..., denomination_multiplier_def, compile_as_wei_value_int_def, compile_floor_def, compile_addmod_def, compile_mulmod_def, compile_pow_mod256_def, compile_select |
| Venom semantics | venom/defs/venomExecSemanticsScript.sml | addmod_def, mulmod_def, safe_sdiv_def, word_exp, exec_pure2/3, ASSERT |
| source | semantics/vyperContextScript.sml, semantics/vyperValueOperationScript.sml | evaluate_builtin_def (AsWeiValue, AddMod, MulMod, PowMod256, Floor), evaluate_as_wei_value_def, decimal_scale; vfmExecution modexp in .holbuild/src/verifereum |
| typing | semantics/type/vyperTypeSystemScript.sml, semantics/prop/vyperTypeBuiltinsScript.sml | well_typed_builtin_app_def, builtin typing lemmas |

## Notes

Analysis of why each case holds is in a comment above the arithmetic lemmas in lowering/exprSimBuiltinsScript.sml.
