# TASK: Prove counted simulation for a word local

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/exprSimNameWordScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_name_word_sim:
  !ctx func cenv cx ty ann id es p sz entry.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    is_word_type ann /\
    lookup_scopes id es.scopes = SOME entry /\ word_value entry.value ==>
    expr_sim ctx func cenv cx ty (Name ann id) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build exprSimNameWordTheory` passes with the assigned root.
2. No new admissions, axioms, parser warnings, timeout overrides or search-filtering TRY/ORELSE.
3. All existing definitions and other theorem statements remain unchanged. Search for existing facts and reuse them; export or move matching local facts instead of duplicating them.

## Build

```sh
holbuild -j2 build exprSimNameWordTheory
```

## Background

The shared expression judgment now counts actual target GAS events and selects explicit source readings, preserving full posts and exact cursors. This existing leaf statement was moved unchanged out of the old monolithic expression theory; its old proof remains and needs migration. The generic normal-value introduction now requires an actual gas_value_prefix F, rather than an uncounted continuation fragment.

## Domain Constraints

Independent statement audit answered PROVABLE for the exact root under the current definitions. Preserve all concrete entry conditions, universal source admissibility before witnesses, all-tail source execution, actual target paths and strict complete expression posts/cursors. No generic frag_exec-to-gas_path converse, new theorem premise, source evaluator, oracle-matching guard, opcode restriction or memory exemption. Other independent main roots are outside scope.

## Available Resources

- lowering/exprSimNameWordScript.sml: single assigned root and retained proof.
- lowering/exprSimDefsScript.sml, exprSimValuesScript.sml, gasNormalPrefixScript.sml: actual counted judgment and normal-prefix introduction.
- lowering/exprSimPropsScript.sml, exprLoweringPropsScript.sml, loweringPostsScript.sml: existing full-post and frame facts.
- lowering/fragGasPathScript.sml, gasSummaryScript.sml: actual paths, selected marks and source execution.
- lowering/defs/exprLoweringScript.sml, emitHelperScript.sml, compileEnvScript.sml: actual compiler and entries.
- semantics/vyperInterpreterScript.sml and semantics/vyperStateScript.sml: actual source evaluation.

## Notes

The root and retained proof are byte-identical to the original. Parser build 58982 reached the Name and Literal roots and failed in their retained uncounted proofs; Env was not reached before the build stopped. Its independently checked statement is the launch prerequisite. Frozen definitions include expr_sim, expr_sim_values, gas_value_prefix, all actual executable definitions and their existing result/post domains.
