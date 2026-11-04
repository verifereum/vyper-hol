# TASK: Prove counted raw local-name value simulation

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/exprSimNameValueScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_name_vv_sim:
  !cenv ann id. expr_vv_ok cenv (Name ann id)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build exprSimNameValueTheory` passes with the exact assigned root.
2. No admissions, axioms, parser warnings, timeout overrides or TRY/ORELSE around proof search.
3. Preserve all definitions and existing theorem statements. Reuse, move or export existing matching facts instead of duplicating them.

## Build

```sh
holbuild -j2 build exprSimNameValueTheory
```

## Background

The raw expression judgment now selects source gas observations from an actual counted target prefix. This exact existing local-name theorem and its old proof were extracted from exprSimLeaves into an independent owner. The theorem covers local values of every type, while the separate checked exprSimNameWord handles forcing word locals.

## Domain Constraints

Preserve universal source admissibility, every unused source tail, the actual target path and full vv_post, including local regions, allocations and cursor. No executable-definition or theorem-premise changes, new exception exemption, arbitrary source certificate or supported-subset restriction. General unwrap and other expression leaves are outside scope. Search existing common ancestors before adding any helper.

## Available Resources

- lowering/exprSimNameValueScript.sml: exact root with retained proof.
- lowering/exprSimHypsDefsScript.sml: expr_vv_ok, typing and local-pointer invariant.
- lowering/exprSimDefsScript.sml, lowering/loweringPostsScript.sml: counted raw judgment and full value post.
- lowering/exprSimPropsScript.sml, lowering/loweringSliceScript.sml: existing source-name, state and value-layout facts.
- lowering/gasOutcomeScript.sml, lowering/gasSummaryScript.sml, lowering/fragGasPathScript.sml: counted execution and actual source action.
- lowering/defs/exprLoweringScript.sml, lowering/defs/compileEnvScript.sml: actual compiler and local-pointer relation.
- semantics/vyperInterpreterScript.sml, semantics/vyperStateScript.sml, semantics/prop/vyperTypeEnvScript.sml: actual source semantics and environment lookup.

## Notes

Independent exact statement audit: PROVABLE, including all source tails, actual empty compilation, local-region bounds and full post. After adding the direct vyperTypeInvariants ancestor, preliminary build64993 parsed the exact root and failed in the retained obsolete uncounted proof. Do not import unported exprSimLeaves, exprSimHyps or exprSimUnwrap to recover obsolete proof adapters. No proof strategy is prescribed.
