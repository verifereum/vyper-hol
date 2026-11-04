# TASK: Repair expression precondition propagation for gas ABI coverage

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/exprSimConvertGasScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem convert_empty_gas_prefix:
  !memory ctx func cenv cx ann ty e es sa s1 sb x op s0 marks v ee t.
    lower_value compile_expr cenv (expr_type e) e sa = (x, s1) /\
    compile_type_convert x (mk_convert_op (expr_type e) ty) s1 = (op, sb) /\
    gas_marked_exec memory (ctx, func)
      (bind (eval_expr cx e) (read_result cx))
      (es, s0) marks (INL v) ee (OK t) /\
    expr_post ctx func cenv cx e es sa s1 s0
      (ee with gas_obs := []) v x t /\
    t.vs_current_bb = s1.cs_current_bb /\
    t.vs_inst_idx = LENGTH s1.cs_current_insts /\
    convert_result cx (expr_type e) ty v =
      INR (Error (RuntimeError "convert empty bytes to signed")) ==>
    gas_marked_exec memory (ctx, func)
      (bind (eval_expr cx (TypeBuiltin ann Convert ty [e])) (read_result cx))
      (es, s0) marks
      (INR (Error (RuntimeError "convert empty bytes to signed"))) ee (OK t) /\
    expr_post ctx func cenv cx e es sa s1 s0
      (ee with gas_obs := []) v x t /\
    t.vs_current_bb = s1.cs_current_bb /\
    t.vs_inst_idx = LENGTH s1.cs_current_insts
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build exprSimConvertGasTheory` passes, retaining the frozen root and all existing ancestor statements and definitions.
2. No new admissions, axioms, parser warnings, timeout overrides or search-filtering TRY/ORELSE. Existing admitted lemmas outside the task remain outside its scope.
3. Reuse existing results; move/export an existing common helper instead of copying it.

## Build

```sh
holbuild -j4 build exprSimConvertGasTheory
```

## Background

The shared expression preconditions now carry ABI target-occurrence coverage and dynamic type-environment compatibility. These obligations are inherited by actual child expressions. Restore the unchanged proofs consuming these preconditions. The latest owner build failed at exprSimOperators.expr_sim_pre_ifexp with a child ABI-target occurrence goal; further consumers may need the same proof-only migration. Do not broaden any precondition or modify statement assumptions to bypass it.

## Domain Constraints

Every executable definition, logical definition and existing theorem statement is frozen. In particular retain expr_sim_pre, expr_body_pre, gas_value_prefix, source cleanup and the two unchanged exemption gates. Repair proofs only, including prerequisite proofs. Preserve ordinary counted paths and the separate memory-safe path mode. No new evaluator, source-equivalence certificate rule, feature restriction or new stage/top-level premise. No replacing existing proof code with cheat. No change to another independent main theorem's statement.

## Available Resources

- lowering/exprSimConvertGasScript.sml: exact frozen root; its proof remains present.
- lowering/exprSimOperatorsScript.sml: current first failing ancestor expr_sim_pre_ifexp.
- lowering/exprSimHypsScript.sml: amended preconditions and checked builtin-child inheritance helpers.
- lowering/supported/supportedExprTraverseScript.sml: actual AST occurrence traversal.
- lowering/supported/supportedProgramScript.sml: actual program ABI-target occurrence.
- lowering/exprSimConvertScript.sml, exprSimAggregateSourceScript.sml, exprSimTupleScript.sml, exprSimSendScript.sml, exprOpenFirstOperandScript.sml: existing proof consumers.
- lowering/gasNormalPrefixScript.sml and gasSummaryScript.sml: unchanged concrete child post and chosen execution mode.

## Notes

The root statement is independently audited PROVABLE. This amended mode root has not yet been parsed because the ancestor proof fails first; its earlier fixed-memory instance was owner checked. The current definitions and syntax-coverage transport were separately audited PROVABLE. Existing proof bodies remain available.
