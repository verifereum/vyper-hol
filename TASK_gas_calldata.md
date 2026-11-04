# TASK: Prove counted simulation for calldata length

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/exprSimCalldataScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_calldatasize_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann CalldataLen args)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build exprSimCalldataTheory` passes with the assigned root.
2. No new admissions, axioms, proof-parser warnings, timeout overrides or search-filtering TRY/ORELSE.
3. All existing definitions and theorem statements remain unchanged. Search for existing facts and reuse them; export or move matching local facts instead of duplicating them.

## Build

```sh
holbuild -j2 build exprSimCalldataTheory
```

## Background

The shared expression judgment counts actual target GAS events and selects source explicit readings, retaining full expression posts and exact cursors. This existing root still has its uncounted continuation-fragment proof. Its pure compiler/evaluation prerequisites have been retained unchanged and their common facts moved beside the definitions they describe.

## Domain Constraints

Independent statement audit answered PROVABLE for the exact root under the current definitions. Preserve the concrete entry relation, universal source admissibility before witnesses, all-tail source execution, actual target paths, complete expression post and cursor. No generic uncounted-fragment converse, new theorem premise, source evaluator, oracle-matching guard, opcode restriction or memory exemption. Other main simulation roots are outside scope.

## Available Resources

- lowering/exprSimCalldataScript.sml: assigned root, retained proof and existing pure calldata lemmas.
- lowering/exprSimDefsScript.sml, lowering/exprSimValuesScript.sml, lowering/gasNormalPrefixScript.sml: actual counted judgment and normal-prefix introduction.
- lowering/exprSimHypsDefsScript.sml: expression preconditions, expr_ok_stack and builtin-dispatch facts.
- lowering/exprSimEnvScript.sml, lowering/emitHelperPropsScript.sml: checked zero-GAS environment simulation and shared emit_op_zero_path.
- lowering/exprSimPropsScript.sml, lowering/exprLoweringPropsScript.sml, lowering/loweringPostsScript.sml: complete postconditions and frame facts.
- lowering/fragGasPathScript.sml, lowering/gasSummaryScript.sml: actual target paths and source execution.
- lowering/defs/exprLoweringScript.sml, lowering/defs/emitHelperScript.sml, lowering/defs/compileEnvScript.sml: actual compiler and entries.
- semantics/vyperInterpreterScript.sml, semantics/vyperStateScript.sml: actual source evaluation.

## Notes

The exact root and its retained proof are unchanged. The owner build parsed the root and reached the retained uncounted proof's `frag_exec` step, which no longer matches the required `gas_value_prefix`. The independent audit covers the actual current counted definitions. All existing executable definitions, judgment definitions, postcondition domains and theorem statements are frozen.
