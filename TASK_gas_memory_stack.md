# TASK: Preserve raw stack results in counted memory simulation

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/exprSimMemoryStackScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem body_expr_vv_sim_mem_stack:
  expr_sim_mem ctx func cenv cx ty e es /\
  (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op,sb)) /\
  (!s tv es'. eval_expr cx e s = (INL tv,es') ==> ?v. tv = Value v) ==>
  expr_vv_sim_mem ctx func cenv cx ty e es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build exprSimMemoryStackTheory` passes with its frozen theorem.
2. Preserve every definition and existing theorem statement. No new admission, axiom, timeout override, feature restriction or TRY/ORELSE around search.
3. Retain the complete raw expression postcondition, exact cursor, allocation history, frontier monotonicity, actual counted memory execution, exception branches and concrete exemption certificates.
4. No let expressions in new theorem statements. Search and reuse existing facts before adding helpers.

## Build

```sh
holbuild -j2 build exprSimMemoryStackTheory
```

## Background

The shared memory judgments now use actual counted execution and existential source observations. This existing stack adapter moves from its body-level owner into a common ancestor beside those judgments. Its raw-success premise quantifies arbitrary source states, matching the ordinary counted stack adapter and the concrete environment, flag and calldata producers.

## Domain Constraints

Only the stack-adapter proof and necessary reusable helpers are in scope. Do not change executable definitions, judgment definitions, source or target oracle policies, source exemption semantics, or another construct proof. Full memory posts and history must remain in the conclusion. Existing ordinary helpers are dependencies to reuse, not duplicate.

## Available Resources

- lowering/exprSimMemoryStackScript.sml: frozen root and preserved legacy proof.
- lowering/exprSimMemDefsScript.sml: complete counted memory expression judgments.
- lowering/exprSimStackScript.sml: ordinary counted stack transport and source forcing facts.
- lowering/exprSimDefsScript.sml: raw and forced result domains.
- lowering/loweringPostsScript.sml: complete value and raw-value postconditions.
- lowering/gasOutcomeScript.sml, lowering/gasSummaryScript.sml, lowering/gasSummaryComposeScript.sml: counted execution and monadic composition.
- lowering/gasExemptCertScript.sml, lowering/gasContextScript.sml: concrete certificate transport and admissibility.

## Notes

Build 66798 parsed this root, then its retained uncounted proof failed at Cases_on `res`: the counted judgment no longer binds a predetermined result. A fresh independent definition audit answered PROVABLE with the complete memory post and certificate intact. The premise amendment is awaiting confirmation before launch. No proof strategy is prescribed.
