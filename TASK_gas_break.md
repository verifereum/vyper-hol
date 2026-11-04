# TASK: Prove counted simulation for loop break

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/stmtSimBreakScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_break_frag:
  !ctx func cx RetQ cenv ty ex inc es.
    stmt_frag ctx func cx (InLoop ex inc) RetQ cenv
      (stmt_env cenv (InLoop ex inc) ty Break)
      (eval_stmt cx Break) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build stmtSimBreakTheory` passes with the assigned root.
2. No new admissions, axioms, parser warnings, timeout overrides or search-filtering TRY/ORELSE.
3. All definitions and other theorem statements remain unchanged. Search for existing facts and reuse them; export or move matching local facts instead of duplicating them.

## Build

```sh
holbuild -j2 build stmtSimBreakTheory
```

## Background

The statement judgment now runs the actual source action with selected readings from a counted target prefix, preserving full posts and exact cursors. This root's retained proof targets the old original-oracle judgment and needs migration. The ordinary and memory path relations now also permit stopping at the actual raw non-INVOKE jump endpoint, while preserving their existing entered-target branch and conditional full execution theorem.

## Domain Constraints

Independent required statement audit answered PROVABLE for this exact statement and current definitions. Preserve universal source admissibility before witnesses, actual source action, all-tail source result, concrete counted target path and every full post/frame/cursor field. No destination-present/zero-PHI premise, generic frag_exec-to-path converse, new source evaluator, oracle equality, opcode restriction or memory-history requirement. Other independent main roots are outside scope.

## Available Resources

- lowering/stmtSimBreakScript.sml: assigned root and retained proof.
- lowering/stmtSimDefsScript.sml, stmtSimPropsScript.sml, loweringPostsScript.sml: actual statement contract and full posts.
- lowering/gasOutcomeScript.sml, gasSummaryScript.sml, gasContextScript.sml: actual counted outcome and source admissibility.
- lowering/fragGasPathScript.sml, fragExecScript.sml: raw actual jump endpoints and full continuations.
- lowering/stmtSimZeroScript.sml, exprLoweringPropsScript.sml: existing strict posts and source gas-state frame.
- lowering/defs/stmtLoweringScript.sml, emitHelperScript.sml, compileEnvScript.sml: compiler and entry conditions.
- semantics/vyperInterpreterScript.sml, semantics/vyperStateScript.sml: actual source action.

## Notes

Definitions and frozen root are not to be restated. Parser build 59767 built the actual counted ancestors but ML compilation stopped at missing imports in the retained legacy proof. Those direct imports are now present; the root has not yet been parsed. The independent statement audit answered PROVABLE against the actual definitions.
