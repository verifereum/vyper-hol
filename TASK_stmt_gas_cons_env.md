# TASK: Prove counted statement sequencing at the compiled environment

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/stmtSimSeqEnvScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem stmt_frag_cons_env:
  !ctx func cx lctx RetQ cenv ty stmt ss es.
    (!c. cs_mono (compile_stmt c lctx ty stmt)) /\
    (!c. cs_mono (stmts_env c lctx ty ss)) /\
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty stmt)
      (eval_stmt cx stmt) es /\
    (!gs es1 c sa sm.
       eval_stmt cx stmt (es with gas_obs := gs) = (INL (), es1) /\
       stmt_env cenv lctx ty stmt sa = (c, sm) /\
       cenv_top_ext cenv c es1.scopes ==>
       stmt_frag ctx func cx lctx RetQ c (stmts_env c lctx ty ss)
         (eval_stmts cx ss) es1) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmts_env cenv lctx ty (stmt::ss)) (eval_stmts cx (stmt::ss)) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build stmtSimSeqEnvTheory` passes with the frozen theorem.
2. No new admissions, axioms, parser warnings, timeout overrides or search-filtering TRY/ORELSE.
3. Keep all existing definitions and theorem statements unchanged. Reuse existing facts; move or export existing local facts instead of duplicating them.

## Build

```sh
holbuild -j2 build stmtSimSeqEnvTheory
```

## Background

The statement judgment now takes the actual source action and counts target GAS events, selecting only explicit source reads. This list rule's continuation ranges over every replacement source oracle. It retains the actual environment produced by compiling the head and the complete statement post, including control landings and all-tail return checks. The old proof is retained and needs migration.

## Domain Constraints

The exact statement was independently audited PROVABLE. All definitions and other existing theorem statements are frozen. Preserve modes, strict full posts, concrete entry before selected marks, actual source actions, exact error-origin certificates and their existing gates. No evaluator replacement, arbitrary source-equivalence certificate, opcode-absence restriction or stage/top-level premise. Other independent main roots are outside scope.

## Available Resources

- lowering/stmtSimSeqEnvScript.sml: single assigned main theorem and retained proof.
- lowering/stmtSimPropsScript.sml: existing compiled-environment, reservation and frame facts, moved without restatement.
- lowering/stmtSimDefsScript.sml and loweringPostsScript.sml: actual counted judgments, full posts and compiler wrappers.
- lowering/gasOutcomeScript.sml, gasSummaryScript.sml and gasSummaryComposeScript.sml: selected readings and actual execution composition.
- lowering/gasExemptCertScript.sml: frozen concrete error transport rules.
- semantics/vyperInterpreterScript.sml and prop/vyperEvalPreservesScopesScript.sml: actual statement evaluation and scope-domain preservation.

## Notes

The exact statement and actual definitions were independently audited PROVABLE before launching. Its uniform-gas continuation is approved and does not introduce a new stage or top-level premise. The exact root is awaiting its parser build; the new statement definition theory already built. Do not replace the retained proof by an admission.
