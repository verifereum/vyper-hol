# TASK: Prove counted simulation for bare and unreachable raise

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/stmtSimRaiseScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_raise_frag:
  !ctx func cx lctx RetQ cenv ty rk es.
    (rk = RaiseBare \/ rk = RaiseUnreachable) ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Raise rk))
      (eval_stmt cx (Raise rk)) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build stmtSimRaiseTheory` passes with the assigned root.
2. No new admissions, axioms, proof-parser warnings, timeout overrides or search-filtering TRY/ORELSE.
3. All existing definitions and other theorem statements remain unchanged. Reuse existing facts; export or move matching local facts instead of duplicating them.

## Build

```sh
holbuild -j2 build stmtSimRaiseTheory
```

## Background

The shared statement judgment simulates the actual source action under selected explicit gas readings. This existing raise helper now passes eval_stmt as its source action, replacing obsolete fixed result/state parameters and their evaluation premise. Its two existing raise forms and all other hypotheses are retained. The old proof remains. Shared abort and primitive execution helpers have been moved unchanged from stmtSimIf to their common owners.

## Domain Constraints

Independent statement audit answered PROVABLE for this exact root under current definitions. Preserve universal source admissibility before witnesses, every source oracle tail, actual counted terminal execution and the full statement exit post. Keep existing strict summaries and concrete certificate constructors. No new theorem premise, evaluator, source-equivalence certificate, opcode restriction, source-reading shortcut or exception exemption. If/Assert and other statement roots are outside this task.

## Available Resources

- lowering/stmtSimRaiseScript.sml: exact assigned root and retained proof.
- lowering/stmtSimDefsScript.sml, lowering/stmtSimPropsScript.sml, lowering/loweringPostsScript.sml: actual statement judgment, post and common emitted-abort fact.
- lowering/emitHelperPropsScript.sml: existing primitive zero-revert and invalid facts, exported without restatement.
- lowering/fragGasPathScript.sml, lowering/gasCountScript.sml: actual target paths and GAS counts.
- lowering/gasOutcomeScript.sml, lowering/gasSummaryScript.sml, lowering/gasContextScript.sml: strict source-action and terminal summary.
- lowering/defs/stmtLoweringScript.sml, lowering/defs/emitHelperScript.sml, lowering/defs/compileEnvScript.sml: actual compiler and entries.
- semantics/vyperInterpreterScript.sml, semantics/vyperStateScript.sml: actual source evaluation.

## Notes

The shared prerequisites built. The restated root parsed in the owner build, then its retained old proof failed at the expected statement-wrapper mismatch. The independent exact statement audit is complete. All source/target executable definitions, gas judgments, strict postconditions and error gates are frozen. No proof strategy is prescribed.
