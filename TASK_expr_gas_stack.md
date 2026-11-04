# TASK: Prove the counted stack-expression adapter

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/exprSimStackScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem expr_vv_sim_stack:
  !ctx func cenv cx ty e es.
    expr_sim ctx func cenv cx ty e es /\
    (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op, sb)) /\
    (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
    expr_vv_sim ctx func cenv cx ty e es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build exprSimStackTheory` passes with the frozen theorem.
2. No new admissions, axioms, parser warnings, timeout overrides, search-filtering TRY/ORELSE, or changed existing definitions or theorem statements.
3. Reuse existing theorems. Export or move an existing helper instead of duplicating it, including local copies.

## Build

```sh
holbuild -j2 build exprSimStackTheory
```

## Background

The shared expression judgments now carry fixed-mark counted source/target execution. This adapter transfers the forced-value judgment to the raw-expression judgment for code whose compiled value is always a StackValue. The source's normal raw results are Values at every source state. The old proof is retained but refers to the previous judgment and needs migration.

## Domain Constraints

All definitions and existing theorem statements are frozen. Preserve the universal entry admissibility before chosen marks, full normal postconditions and exact landings, and the concrete exception-certificate alternative. Preserve the actual source action, existing exemption gates, mode F and context-derived program. No arbitrary source-equivalence certificate rule, new evaluator, restriction, or new stage/top-level premise. The theorem is independently audited PROVABLE. Other independent main theorems, including internal-call transport, are outside this task.

## Available Resources

- lowering/exprSimStackScript.sml: the single assigned main theorem and retained old proof.
- lowering/exprSimDefsScript.sml: frozen shared judgments and result domains; the two existing exit lemmas moved unchanged.
- lowering/gasOutcomeScript.sml: strict or concretely exempt outcome.
- lowering/gasSummaryScript.sml and gasSummaryComposeScript.sml: actual fixed-mark executions and their composition.
- lowering/gasExemptCertScript.sml: concrete exception certificate; its constructors are frozen.
- lowering/loweringPostsScript.sml: full expr_post/vv_post and StackValue relations.
- semantics/vyperInterpreterScript.sml and semantics/vyperStateScript.sml: actual evaluation and monadic operations.

## Notes

The shared definitions and this exact theorem were independently audited PROVABLE; dependency closure is acyclic. The shared definition theory built with all six definitions and both moved exit theorems saved. The exact root parsed; its retained proof fails at its old Cases_on `res`, because the source result is now selected inside gas_outcome. Existing proof bodies remain available and must not be replaced by admissions. Other legacy exprSim helpers have not yet been migrated and are deliberately not ancestors of this independent adapter. exprSimValues is a separate independent introduction helper and is outside this task.
