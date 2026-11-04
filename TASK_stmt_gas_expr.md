# TASK: Prove counted expression statements

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: lowering/stmtSimExprScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_expr_stmt_frag_ok:
  !ctx func cx lctx RetQ cenv ty e es.
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    (!gs sa vv sb tv es1.
       storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
       eval_expr cx e (es with gas_obs := gs) = (INL tv, es1) /\
       compile_expr cenv (expr_type e) e sa = (vv, sb) /\
       ~block_is_terminated sa ==> ~block_is_terminated sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Expr e))
      (eval_stmt cx (Expr e)) es

Theorem compile_expr_stmt_frag:
  !ctx func cx lctx RetQ cenv ty e es.
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    (!sa vv sb. compile_expr cenv (expr_type e) e sa = (vv, sb) /\
                ~block_is_terminated sa ==> ~block_is_terminated sb) ==>
    stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Expr e))
      (eval_stmt cx (Expr e)) es
```

Do not modify these statements. Prove them as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j2 build stmtSimExprTheory` passes with the assigned root and its dependent unconditional-openness wrapper.
2. No new admissions, axioms, parser warnings, timeout overrides or search-filtering TRY/ORELSE.
3. Keep all existing definitions and other theorem statements unchanged. Search and reuse existing facts; export or move existing local facts rather than duplicating them.

## Build

```sh
holbuild -j2 build stmtSimExprTheory
```

## Background

Statement simulation now takes the actual source action, counts all target GAS events, selects explicit source readings, and retains strict full posts and tail-universal terminal exits. The raw-expression simulation already uses this counted judgment. The normal-result openness premise ranges over every replacement source gas list. The first root needs migration; the second is its direct wrapper with unconditional compiler openness. Their old proofs are retained.

## Domain Constraints

Both exact statements were independently audited PROVABLE. All definitions and other existing statements are frozen. Retain concrete entry/admissibility before selected witnesses, exact posts/cursors/frames, actual source evaluation and the existing concrete exception certificate rules/gates. No new arbitrary source-equivalence certificate rule, replacement evaluator, excluded opcode, or stage/top-level premise. Other independent main roots are outside scope.

## Available Resources

- lowering/stmtSimExprScript.sml: assigned root and dependent wrapper, retained proofs.
- lowering/stmtSimDefsScript.sml, exprSimDefsScript.sml, loweringPostsScript.sml: actual counted judgments, full posts and compiler wrappers.
- lowering/stmtSimPropsScript.sml, exprSimPropsScript.sml: existing pure support facts.
- lowering/gasOutcomeScript.sml, gasSummaryScript.sml, gasSummaryComposeScript.sml, gasExemptCertScript.sml: frozen selected-reading and concrete exemption machinery.
- semantics/vyperInterpreterScript.sml, semantics/prop/vyperExprNoControlScript.sml: actual expression-statement evaluation and expression exception domain.
- semantics/vyperStateScript.sml: source monadic laws. Do not duplicate existing associativity laws, including ignore_bind_assoc if applicable.

## Notes

The exact first root parsed in owner build58429; its retained proof fails at the early strip_tac because stmt_frag now unfolds to the framed judgment. The dependent wrapper has not been parsed past that first failure. Independent audit checked both exact statements against the actual definitions. No root proof has been replaced by an admission. Source-action and universal-gas openness restatements have internal approval.
