# TASK: Prove the counted empty-statement fragment

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/stmtSimZeroScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem stmt_frag_nil:
  !ctx func cx lctx RetQ cenv ty es.
    stmt_frag ctx func cx lctx RetQ cenv (stmts_env cenv lctx ty [])
      (eval_stmts cx []) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build stmtSimZeroTheory` passes with the frozen theorem.
2. No new admissions, axioms, parser warnings, timeout overrides or search-filtering TRY/ORELSE.
3. Keep all existing definitions and theorem statements unchanged. Reuse existing facts; move or export existing local facts instead of duplicating them.

## Build

```sh
holbuild -j2 build stmtSimZeroTheory
```

## Background

The shared statement judgment now takes the actual source action, with fixed-mark counted execution. Normal outcomes retain the full environment, frame and cursor post. Terminal outcomes retain all-tail return checks. This root handles the empty list with the ordinary mode. Its existing migrated proof is retained and does not yet close the full post.

## Domain Constraints

All definitions are frozen. Preserve universal admissibility before selected readings, actual source actions, full posts and the existing concrete exemption gates. Do not add allocation-history premises, replace the evaluator, invent a source-equivalence certificate constructor, restrict the program or introduce stage/top-level assumptions. Other independent roots are outside scope.

## Available Resources

- lowering/stmtSimZeroScript.sml: single assigned main root and the checked framed-zero adapter.
- lowering/stmtSimDefsScript.sml: counted statement judgments, result domain and posts.
- lowering/loweringPostsScript.sml: compiler wrappers and frame predicates.
- lowering/gasSummaryScript.sml, gasOutcomeScript.sml, fragGasModeScript.sml and fragGasPathScript.sml: fixed-mark execution.
- lowering/exprLoweringPropsScript.sml and defs/compileEnvScript.sml: source/target frame relations.
- semantics/vyperInterpreterScript.sml and vyperStateScript.sml: actual source evaluation.

## Notes

The exact root was independently audited PROVABLE, with no missing premise. Its exact statement parsed in the owner build. The new definition theories built and saved their definitions. The retained proof failed while closing the full normal post; no temporary admission replaced it. The ordinary mode requires no initial allocation history. Do not work on stmtSimPass, sequence composition or other independent roots.
