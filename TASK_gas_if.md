# TASK: Prove counted actual-source simulation for an if statement

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/stmtSimIfCountedScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_if_stmt_frag:
  !ctx func cx lctx RetQ cenv ty c ss1 ss2 es.
    expr_type c = BaseT BoolT /\
    expr_sim ctx func cenv cx (BaseT BoolT) c es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
                cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    cs_mono (stmts_env cenv lctx ty ss1) /\
    cs_mono (stmts_env cenv lctx ty ss2) /\
    (!gs b es1.
       (do result <- eval_expr cx c; read_result cx result od)
         (es with gas_obs := gs) = (INL (BoolV b), es1) ==>
       stmt_frag ctx func cx lctx RetQ cenv
         (stmts_env cenv lctx ty (if b then ss1 else ss2))
         (eval_stmts cx (if b then ss1 else ss2))
         (es1 with scopes := FEMPTY :: es1.scopes)) ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (If c ss1 ss2))
      (eval_stmt cx (If c ss1 ss2)) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build stmtSimIfCountedTheory` passes with the assigned root.
2. No new admissions, axioms, proof-parser warnings, timeout overrides or TRY/ORELSE around search tactics.
3. All definitions and other existing theorem statements remain unchanged. Search for existing facts before adding helpers; export or move matching local facts rather than duplicating them.

## Build

```sh
holbuild -j2 build stmtSimIfCountedTheory
```

## Background

The statement judgment now consumes the actual source action under selected explicit gas readings. This existing root has been mechanically restated to pass eval_stmt as that action, removing obsolete fixed source result/state parameters and their evaluation premise. Its old proof remains. The If branch induction premise now quantifies over every replacement source gas list and supplies the selected actual-source branch judgment. All other hypotheses are retained. Existing pure source/compiler decomposition facts have moved unchanged into stmtSimIfProps, with local facts exported for actual separate consumers.

## Domain Constraints

Independent exact statement audit answered PROVABLE. The uniform If branch premise was approved after checking the actual existing body_if_case producer. Preserve universal source admissibility before target witnesses, every unused source tail, actual target GAS counts and control-flow steps, exact cursors, full posts and scope cleanup, all RetQ tails, and the existing concrete exception certificate gates. No new theorem premise, evaluator, source-equivalence certificate, opcode restriction, or exception exemption. Only the assigned root is in scope; do not attempt the independent other conditional or raise root.

## Available Resources

- lowering/stmtSimIfCountedScript.sml: assigned root and retained old proof.
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

The parser owner is checking the shared prerequisites and the restated root; if it stops before that root, the statement has not yet been parsed. Independent exact statement audit is complete. Existing executable definitions, gas judgments, strict posts and concrete error gates are frozen. No proof strategy is prescribed.
