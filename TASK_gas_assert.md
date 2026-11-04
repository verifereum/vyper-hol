# TASK: Prove counted actual-source simulation for bare and unreachable assertions

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/stmtSimAssertScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_assert_frag:
  !ctx func cx lctx RetQ cenv ty e ak es.
    (ak = AssertBare \/ ak = AssertUnreachable) /\
    expr_type e = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) e es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) e sa = (op, sb) ==>
                cs_extends sa sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Assert e ak))
      (eval_stmt cx (Assert e ak)) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build stmtSimAssertTheory` passes with the assigned root.
2. No new admissions, axioms, proof-parser warnings, timeout overrides or TRY/ORELSE around search tactics.
3. All definitions and other existing theorem statements remain unchanged. Search for existing facts before adding helpers; export or move matching local facts rather than duplicating them.

## Build

```sh
holbuild -j2 build stmtSimAssertTheory
```

## Background

The statement judgment now consumes the actual source action under selected explicit gas readings. This existing root has been mechanically restated to pass eval_stmt as that action, removing obsolete fixed source result/state parameters and their evaluation premise. Its old proof remains. The If branch induction premise now quantifies over every replacement source gas list and supplies the selected actual-source branch judgment. All other hypotheses are retained. Existing pure source/compiler decomposition facts have moved unchanged into stmtSimIfProps, with local facts exported for actual separate consumers.

## Domain Constraints

Independent exact statement audit answered PROVABLE. The uniform If branch premise was approved after checking the actual existing body_if_case producer. Preserve universal source admissibility before target witnesses, every unused source tail, actual target GAS counts and control-flow steps, exact cursors, full posts and scope cleanup, all RetQ tails, and the existing concrete exception certificate gates. No new theorem premise, evaluator, source-equivalence certificate, opcode restriction, or exception exemption. Only the assigned root is in scope; do not attempt the independent other conditional or raise root.

## Available Resources

- lowering/stmtSimAssertScript.sml: assigned root and retained old proof.
- lowering/stmtSimIfPropsScript.sml: existing source forcing and compiler decomposition facts.
- lowering/stmtSimPropsScript.sml, lowering/stmtSimDefsScript.sml, lowering/loweringPostsScript.sml: actual statement judgment, full posts and shared path/frame helpers.
- lowering/exprSimDefsScript.sml, lowering/exprSimPropsScript.sml: counted expression boundary.
- lowering/gasOutcomeScript.sml, lowering/gasSummaryScript.sml, lowering/gasSummaryComposeScript.sml: strict source-action composition.
- lowering/gasExemptCertScript.sml, lowering/gasContextScript.sml: concrete certificates and universal admissibility.
- lowering/fragGasPathScript.sml, lowering/gasCountScript.sml: actual target paths and counts.
- lowering/defs/stmtLoweringScript.sml, lowering/defs/exprLoweringScript.sml, lowering/emitHelperPropsScript.sml: actual compiler and execution helpers.
- semantics/vyperInterpreterScript.sml, semantics/vyperStateScript.sml: actual source evaluation and cleanup.
- lowering/stmtSimIfScript.sml: original unported intermediate proof text for reference only; it is not an ancestor of the new root.

## Notes

The shared prerequisites and stmtSimIfProps built. ML compilation of the retained old proof stopped at its reference to unported cond_jump_frag, so the assigned root has not yet been parsed. Its independent exact statement audit is complete. That old fixed-result intermediate contract is reference text, not a dependency of the actual-source proof. Existing executable definitions, gas judgments, strict posts and concrete error gates are frozen. No proof strategy is prescribed.
