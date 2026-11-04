# TASK: Prove counted flag-member expression simulation

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/exprSimFlagWordScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_flag_member_word_sim:
  !cenv ann nsid mid. expr_sim_ok cenv (FlagMember ann nsid mid)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build exprSimFlagWordTheory` passes with the assigned root and its existing two wrappers.
2. No admissions, axioms, parser warnings, timeout overrides, or TRY/ORELSE around search.
3. Preserve every definition and existing theorem statement. Search before adding helpers; move or export existing matching facts instead of duplicating them.

## Build

```sh
holbuild -j2 build exprSimFlagWordTheory
```

## Background

The shared expression judgment now chooses source gas readings from the counted target prefix. This existing flag-member theorem keeps its exact statement and original proof. Its source evaluation and emitted literal do not consume gas. The root and its two wrappers have been extracted from exprSimLeaves into an independent owner; its existing source-evaluation fact moved to exprSimProps; other leaf cases are outside this task.

## Domain Constraints

An independent statement audit answered PROVABLE for this exact theorem and both wrappers against the current definitions. Preserve universal source admissibility before selecting witnesses, every unused source tail, the actual counted target execution, and the full expression postcondition including local, variable and allocation frames. No executable-definition or theorem-premise changes, no feature restrictions, no new exception exemptions or certificate constructors. Existing source facts may be moved to a suitable common ancestor if needed, without changing their statement or duplicating them.

## Available Resources

- lowering/exprSimFlagWordScript.sml: exact root, retained proof and wrappers.
- lowering/exprSimHypsDefsScript.sml: expression preconditions and flag-index invariant.
- lowering/exprSimValuesScript.sml, lowering/gasNormalPrefixScript.sml: counted normal-value interface.
- lowering/exprSimDefsScript.sml, lowering/loweringPostsScript.sml: shared judgment and full postcondition.
- lowering/exprSimPropsScript.sml, lowering/exprSimStackScript.sml: existing leaf/source and stack-valued facts.
- lowering/fragGasPathScript.sml, lowering/gasSummaryScript.sml: target paths and marked execution.
- lowering/defs/exprLoweringScript.sml, lowering/defs/compileEnvScript.sml: actual compiler.
- semantics/vyperInterpreterScript.sml, semantics/vyperStateScript.sml: actual source semantics.
- semantics/prop/vyperTypeEnvScript.sml: typing environment facts.

## Notes

The independent audit checked actual typing/module lookup, flag index agreement, source evaluation for all substituted gas tails, zero emitted instructions and complete postcondition preservation. Preliminary build 63856 parsed the exact root and reached its retained proof, which failed because it still concludes the uncounted fragment judgment. The moved source-evaluation fact built successfully before that failure. No proof strategy is prescribed. Other leaf roots remain outside scope.
